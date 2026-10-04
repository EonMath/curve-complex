import CurveComplexGenusTwo.Topology.ActualCutRecognition.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import CurveComplexGenusTwo.Topology.GlobalMonodromy.GlobalLoopSubdivision
import ClassificationOfSurfaces.Moise.GraphPolygonalization
import CurveComplexGenusTwo.Topology.SourceCycleActual.SourceEssentialCurveComplete
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryInput
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceTwoArcParameterizedCurve

open Set Topology unitInterval Schoenflies
open CurveComplex.BranchedDoubleCover
open CurveComplexGenusTwo.SourceTopology

namespace CurveComplex.Hyperbolic
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Proposed geometric producer, awaiting statement review.
The original c is retained literally; b is an actual embedded circle on E.
No path, collar, dual curve, cut surface or crossing certificate is supplied. -/
theorem actual_nondividing_essential_curve_has_single_crossing_dual
    (M : HyperellipticModel E S) (c : Curve E) (hc : Essential c)
    (hndiv : ¬ DividingCurve c) :
    ∃ b : Curve E, ∃ ht : Transverse c b, ht.1.toFinset.card = 1 := by
  classical
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have surfaceArc (U : Set E) (hU : IsOpen U) (hc : IsConnected U)
      (x y : E) (hx : x ∈ U) (hy : y ∈ U) (hne : x ≠ y) :
      ∃ r : Path x y, Function.Injective r ∧ range r ⊆ U := by
    classical
    have join {x y z : E} (p : Path x y) (q : Path y z)
        (hp : Function.Injective p) (hq : Function.Injective q) (hxz : x ≠ z) :
        ∃ r : Path x z, Function.Injective r ∧ range r ⊆ range p ∪ range q := by
      classical
      by_cases hx : x ∈ range q
      · obtain ⟨u, hu⟩ := hx
        have hu1 : u < 1 := lt_of_le_of_ne u.property.2 (by
          intro he
          have he' : u = 1 := he
          exact hxz (hu.symm.trans (he' ▸ q.target)))
        let r := (actualSubpath q u 1).cast hu.symm q.target.symm
        refine ⟨r, (actual_cut_subpath_injective q hq u 1 hu1).1, ?_⟩
        rintro w ⟨t,rfl⟩
        exact Or.inr ⟨intervalAffine u 1 t,rfl⟩
      let K : Set I := p ⁻¹' range q
      have hK : IsCompact K := (isCompact_range q.continuous).isClosed.preimage p.continuous |>.isCompact
      have hne : K.Nonempty := ⟨1, by change p 1 ∈ range q; rw [p.target]; exact ⟨0,q.source⟩⟩
      obtain ⟨t, ht, hmin⟩ := hK.exists_isLeast hne
      obtain ⟨u, hu⟩ := ht
      have ht0 : 0 < t := lt_of_le_of_ne t.property.1 (by
        intro he
        have he' : t = 0 := he.symm
        exact hx (by rw [← p.source, ← he']; exact ⟨u,hu⟩))
      let p' := (actualSubpath p 0 t).cast p.source.symm rfl
      have hp' : Function.Injective p' := (actual_cut_subpath_injective p hp 0 t ht0).1
      by_cases hu1 : u = 1
      · have he : p t = z := hu.symm.trans (hu1 ▸ q.target)
        let r := p'.cast rfl he.symm
        refine ⟨r,hp',?_⟩
        rintro w ⟨v,rfl⟩
        exact Or.inl ⟨intervalAffine 0 t v,rfl⟩
      have hult : u < 1 := lt_of_le_of_ne u.property.2 hu1
      let q' := (actualSubpath q u 1).cast hu.symm q.target.symm
      have hq' : Function.Injective q' := (actual_cut_subpath_injective q hq u 1 hult).1
      have hinter : range p' ∩ range q' = {p t} := by
        apply Subset.antisymm
        · rintro w ⟨⟨a,rfl⟩,⟨b,hb⟩⟩
          have haK : intervalAffine 0 t a ∈ K := ⟨intervalAffine u 1 b,hb⟩
          have hea : intervalAffine 0 t a = t := le_antisymm
            (intervalAffine_mem_Icc (show (0:I) ≤ t from t.property.1) a).2 (hmin haK)
          change p (intervalAffine 0 t a) ∈ {p t}
          rw [hea]
          exact mem_singleton _
        · rintro w rfl
          exact ⟨⟨1,p'.target⟩,⟨0,q'.source⟩⟩
      let r := p'.trans q'
      refine ⟨r,LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter p' q' hp' hq' hinter,?_⟩
      rw [Path.trans_range]
      rintro w (⟨v,rfl⟩ | ⟨v,rfl⟩)
      · exact Or.inl ⟨intervalAffine 0 t v,rfl⟩
      · exact Or.inr ⟨intervalAffine u 1 v,rfl⟩
  
    have small (a : E) (ha : a ∈ U) : ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
        ∀ b ∈ V, a ≠ b → ∃ q : Path a b, Function.Injective q ∧ range q ⊆ U := by
      let e := chartAt (EuclideanSpace ℝ (Fin 2)) a
      have hea : a ∈ e.source := mem_chart_source _ a
      have ho := e.isOpen_inter_preimage_symm hU
      have hmem : e a ∈ e.target ∩ e.symm ⁻¹' U :=
        ⟨e.map_source hea, by change e.symm (e a) ∈ U; rw [e.left_inv hea]; exact ha⟩
      obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp ho (e a) hmem
      let V : Set E := e.source ∩ e ⁻¹' Metric.ball (e a) r
      have hV : IsOpen V := e.isOpen_inter_preimage Metric.isOpen_ball
      have hVU : V ⊆ U := by
        rintro b ⟨hb,hbe⟩
        have hh := (hball hbe).2
        change e.symm (e b) ∈ U at hh
        rw [e.left_inv hb] at hh
        exact hh
      refine ⟨V,hV,⟨hea,Metric.mem_ball_self hr⟩,hVU,?_⟩
      intro b hb hab
      let line := Path.segment (e a) (e b)
      have hline (t : I) : line t ∈ Metric.ball (e a) r := by
        apply (convex_ball (e a) r).segment_subset (Metric.mem_ball_self hr) hb.2
        rw [← Path.range_segment]
        exact ⟨t,rfl⟩
      let q : Path a b := {
        toFun t := e.symm (line t)
        continuous_toFun := e.symm.continuousOn.comp_continuous line.continuous
          (fun t => (hball (hline t)).1)
        source' := by rw [line.source,e.left_inv hea]
        target' := by rw [line.target,e.left_inv hb.1] }
      refine ⟨q,?_,?_⟩
      · intro s t he
        apply Path.segment_injective_of_ne (show e a ≠ e b from fun h => hab (e.injOn hea hb.1 h))
        exact e.symm.injOn (hball (hline s)).1 (hball (hline t)).1 he
      · rintro w ⟨t,rfl⟩
        exact (hball (hline t)).2
    let R : Set E := {a | a ∈ U ∧ (a = x ∨ ∃ p : Path x a, Function.Injective p ∧ range p ⊆ U)}
    let N : Set E := U \ R
    have hR : IsOpen R := by
      rw [isOpen_iff_forall_mem_open]
      rintro a ⟨ha,hreach⟩
      obtain ⟨V,hV,haV,hVU,hlocal⟩ := small a ha
      refine ⟨V,?_,hV,haV⟩
      intro b hb
      refine ⟨hVU hb,?_⟩
      by_cases hbx : b = x
      · exact Or.inl hbx
      by_cases hab : a = b
      · exact hab ▸ hreach
      obtain ⟨q,hq,hqU⟩ := hlocal b hb hab
      rcases hreach with rfl | ⟨p,hp,hpU⟩
      · exact Or.inr ⟨q,hq,hqU⟩
      · obtain ⟨r,hr,hrange⟩ := join p q hp hq (Ne.symm hbx)
        exact Or.inr ⟨r,hr,hrange.trans (union_subset hpU hqU)⟩
    have hN : IsOpen N := by
      rw [isOpen_iff_forall_mem_open]
      rintro a ⟨ha,hnot⟩
      obtain ⟨V,hV,haV,hVU,hlocal⟩ := small a ha
      refine ⟨V,?_,hV,haV⟩
      intro b hb
      refine ⟨hVU hb,?_⟩
      intro hbreach
      by_cases hab : a = b
      · exact hnot (hab ▸ hbreach)
      obtain ⟨q,hq,hqU⟩ := hlocal b hb hab
      rcases hbreach.2 with hbx | ⟨p,hp,hpU⟩
      · have hxa : x = b := hbx.symm
        let r := q.symm.cast hxa rfl
        exact hnot ⟨ha,Or.inr ⟨r,hq.comp unitInterval.symm_involutive.injective,by
          change range q.symm ⊆ U
          rw [Path.symm_range]
          exact hqU⟩⟩
      · by_cases hax : a = x
        · exact hnot ⟨ha,Or.inl hax⟩
        obtain ⟨r,hr,hrange⟩ := join p q.symm hp
          (hq.comp unitInterval.symm_involutive.injective) (Ne.symm hax)
        exact hnot ⟨ha,Or.inr ⟨r,hr,hrange.trans (union_subset hpU (by
          rw [Path.symm_range]
          exact hqU))⟩⟩
    have hdis : Disjoint R N := disjoint_left.mpr (fun _ hr hn => hn.2 hr)
    have hcover : U ⊆ R ∪ N := by
      intro a ha
      by_cases har : a ∈ R
      · exact Or.inl har
      · exact Or.inr ⟨ha,har⟩
    rcases hc.isPreconnected.subset_or_subset hR hN hdis hcover with huR | huN
    · rcases (huR hy).2 with hyx | ⟨p,hp,hpU⟩
      · exact (hne hyx.symm).elim
      · exact ⟨p,hp,hpU⟩
    · exact ((huN hx).2 ⟨hx,Or.inl rfl⟩).elim

  have hns : Nonseparating c := by
    simpa only [Nonseparating, DividingCurve, not_not] using hndiv
  let p := c.map (1 : Circle)
  obtain ⟨e,hpe,hep,_,hsquare,haxis⟩ :=
    PositionUniverseV2.position_curve_crosscut_chart E c p (mem_range_self _) univ isOpen_univ (mem_univ _)
  let vertical (t : I) : Plane := Plane.mk 0 (2*(t:ℝ)-1)
  have hvT (t : I) : vertical t ∈ e.target := by
    apply hsquare
    rw [mem_closedSquare_zero_one]
    change max |(0:ℝ)| |2*(t:ℝ)-1| ≤ 1
    rw [max_le_iff]
    exact ⟨by norm_num,abs_le.mpr ⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩
  let a : Path (e.symm (vertical 0)) (e.symm (vertical 1)) := {
    toFun t := e.symm (vertical t)
    continuous_toFun := e.symm.continuousOn.comp_continuous (by fun_prop) hvT
    source' := rfl
    target' := rfl }
  have haI : Function.Injective a := by
    intro s t he
    have hh := congrArg (fun z : Plane => z 1) (e.symm.injOn (hvT s) (hvT t) he)
    dsimp [vertical,Plane.mk] at hh
    apply Subtype.ext
    linarith
  have haE (t : I) : a t ∈ e.source := e.map_target (hvT t)
  have haCoord (t : I) : e (a t) = vertical t := e.right_inv (hvT t)
  have haCurve (t : I) : a t ∈ c.image ↔ (t:ℝ) = 1/2 := by
    rw [haxis _ (haE t),haCoord]
    dsimp [vertical,Plane.mk]
    constructor <;> intro h <;> linarith
  have ha0 : a 0 ∉ c.image := by rw [haCurve]; norm_num
  have ha1 : a 1 ∉ c.image := by rw [haCurve]; norm_num
  obtain ⟨q,hq,hqU⟩ := surfaceArc c.imageᶜ
    (isCompact_range c.embedded.continuous).isClosed.isOpen_compl hns
    (a 0) (a 1) ha0 ha1 (haI.ne zero_ne_one)
  let mid : I := ⟨1/2,by norm_num⟩
  let Aminus : Set E := a '' Icc 0 mid
  let Aplus : Set E := a '' Icc mid 1
  have hAminus : IsCompact Aminus := isCompact_Icc.image a.continuous
  have hAplus : IsCompact Aplus := isCompact_Icc.image a.continuous
  have hqAvoid (r : I) : q r ∉ c.image := hqU (mem_range_self _)
  have hseparate (r : I) : q r ∈ Aminus → q r ∉ Aplus := by
    rintro ⟨v,hv,hvEq⟩ ⟨w,hw,hwEq⟩
    have hvw : v = w := haI (hvEq.trans hwEq.symm)
    have hvm : v = mid := le_antisymm hv.2 (hvw ▸ hw.1)
    exact hqAvoid r (hvEq ▸ (haCurve v).mpr (congrArg Subtype.val hvm))
  let Kplus : Set I := q ⁻¹' Aplus
  have hKplus : IsCompact Kplus := hAplus.isClosed.preimage q.continuous |>.isCompact
  have hKplusNE : Kplus.Nonempty := ⟨1,by
    change q 1 ∈ Aplus
    rw [q.target]
    exact ⟨1,⟨by change (1/2:ℝ) ≤ 1; norm_num,le_rfl⟩,rfl⟩⟩
  obtain ⟨v,hv,hvmin⟩ := hKplus.exists_isLeast hKplusNE
  have hv0 : 0 < v := by
    apply lt_of_le_of_ne v.property.1
    intro he
    have hvzero : v = 0 := Subtype.ext he.symm
    have hq0 : q 0 ∈ Aminus := by
      rw [q.source]
      exact ⟨0,⟨le_rfl,by change (0:ℝ) ≤ 1/2; norm_num⟩,rfl⟩
    exact hseparate 0 hq0 (hvzero ▸ hv)
  let Kminus : Set I := Icc 0 v ∩ q ⁻¹' Aminus
  have hKminus : IsCompact Kminus :=
    isCompact_Icc.inter_right (hAminus.isClosed.preimage q.continuous)
  have hKminusNE : Kminus.Nonempty := ⟨0,⟨⟨le_rfl,hv0.le⟩,by
    change q 0 ∈ Aminus
    rw [q.source]
    exact ⟨0,⟨le_rfl,by change (0:ℝ) ≤ 1/2; norm_num⟩,rfl⟩⟩⟩
  obtain ⟨t,ht,htmax⟩ := hKminus.exists_isGreatest hKminusNE
  have htv : t < v := lt_of_le_of_ne ht.1.2 (by
    intro he
    exact hseparate t ht.2 (he.symm ▸ hv))
  obtain ⟨u,hu,huEq⟩ := ht.2
  obtain ⟨w,hw,hwEq⟩ := hv
  have hum : u < mid := lt_of_le_of_ne hu.2 (by
    intro he
    exact hqAvoid t (huEq ▸ (haCurve u).mpr (congrArg Subtype.val he)))
  have hmw : mid < w := lt_of_le_of_ne hw.1 (by
    intro he
    exact hqAvoid v (hwEq ▸ (haCurve w).mpr (congrArg Subtype.val he.symm)))
  have huw : u < w := hum.trans hmw
  let A := actualSubpath a u w
  let Q := (actualSubpath q t v).cast huEq hwEq
  have hAI : Function.Injective A := (actual_cut_subpath_injective a haI u w huw).1
  have hQI : Function.Injective Q := (actual_cut_subpath_injective q hq t v htv).1
  have hQzero : Q 0 = A 0 := by rw [Q.source,A.source]
  have hQone : Q 1 = A 1 := by rw [Q.target,A.target]
  have hQavoid (r : I) : Q r ∉ c.image := hqAvoid _
  have hcontact (r s : I) (he : A r = Q s) :
      (r = 0 ∧ s = 0) ∨ (r = 1 ∧ s = 1) := by
    by_cases hs0 : s = 0
    · left
      refine ⟨hAI (he.trans (hs0 ▸ hQzero)),hs0⟩
    by_cases hs1 : s = 1
    · right
      refine ⟨hAI (he.trans (hs1 ▸ hQone)),hs1⟩
    have hs0' : 0 < s := lt_of_le_of_ne s.property.1 (Ne.symm hs0)
    have hs1' : s < 1 := lt_of_le_of_ne s.property.2 hs1
    have hbet := actual_cut_subpath_interior_parameter t v s htv hs0' hs1'
    let cutTime := intervalAffine t v s
    let arcTime := intervalAffine u w r
    have hqr : q cutTime = a arcTime := he.symm
    have hcutTimev : cutTime < v := hbet.2
    by_cases harcTime : arcTime ≤ mid
    · have hcutTimeminus : cutTime ∈ Kminus :=
        ⟨⟨cutTime.property.1,hcutTimev.le⟩,⟨arcTime,⟨arcTime.property.1,harcTime⟩,hqr.symm⟩⟩
      exact (not_le_of_gt hbet.1 (htmax hcutTimeminus)).elim
    · have hcutTimeplus : cutTime ∈ Kplus :=
        ⟨arcTime,⟨(not_le.mp harcTime).le,arcTime.property.2⟩,hqr.symm⟩
      exact (not_le_of_gt hcutTimev (hvmin hcutTimeplus)).elim
  obtain ⟨b,hb,_⟩ := two_embedded_arcs_parameterized_curve A Q hAI hQI hcontact
  have hap : a mid = p := by
    change e.symm (vertical mid) = p
    have hmid : vertical mid = 0 := by ext i; fin_cases i <;> norm_num [vertical,Plane.mk,mid]
    rw [hmid,←hep,e.left_inv hpe]
  have hrangeA : range A = a '' Icc u w := by
    apply Subset.antisymm
    · rintro x ⟨r,rfl⟩
      exact ⟨intervalAffine u w r,intervalAffine_mem_Icc huw.le r,rfl⟩
    · rintro x ⟨r,hr,rfl⟩
      let z : I := ⟨((r:ℝ)-(u:ℝ))/((w:ℝ)-(u:ℝ)),by
        have hh : (u:ℝ) < w := huw
        constructor
        · exact div_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hh.le)
        · apply (div_le_one (sub_pos.mpr hh)).mpr
          exact sub_le_sub_right (show (r:ℝ) ≤ (w:ℝ) from hr.2) (u:ℝ)⟩
      refine ⟨z,?_⟩
      change a (intervalAffine u w z) = a r
      congr 1
      apply Subtype.ext
      change (1-(((r:ℝ)-(u:ℝ))/((w:ℝ)-(u:ℝ))))*(u:ℝ) +
        (((r:ℝ)-(u:ℝ))/((w:ℝ)-(u:ℝ)))*(w:ℝ) = (r:ℝ)
      have hden : (w:ℝ)-(u:ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt huw)
      field_simp [hden]
      <;> ring
  have hpA : p ∈ range A := by
    rw [hrangeA,←hap]
    exact ⟨mid,⟨hum.le,hmw.le⟩,rfl⟩
  have hcrossSet : c.image ∩ b.image = {p} := by
    ext x
    constructor
    · rintro ⟨hxc,hxb⟩
      rw [hb] at hxb
      rcases hxb with hxa | ⟨r,hr⟩
      · rw [hrangeA] at hxa
        obtain ⟨r,_,rfl⟩ := hxa
        have hrm : r = mid := Subtype.ext ((haCurve r).mp hxc)
        rw [hrm,hap]
        exact mem_singleton _
      · exact (hQavoid r (hr ▸ hxc)).elim
    · intro hx
      have hxp : x = p := mem_singleton_iff.mp hx
      subst x
      exact ⟨mem_range_self _,by rw [hb]; exact Or.inl hpA⟩
  have hfinite : (c.image ∩ b.image).Finite := hcrossSet ▸ finite_singleton p
  have hcross : CrossesAt c b p := by
    have hpQ : p ∉ range Q := by
      rintro ⟨r,hr⟩
      exact hQavoid r (hr ▸ mem_range_self (1 : Circle))
    let V : Set Plane := {z | 2*(u:ℝ)-1 < z 1 ∧ z 1 < 2*(w:ℝ)-1}
    have hV : IsOpen V := by
      change IsOpen ({z : Plane | 2*(u:ℝ)-1 < z 1} ∩ {z : Plane | z 1 < 2*(w:ℝ)-1})
      exact (isOpen_lt continuous_const (by fun_prop)).inter
        (isOpen_lt (by fun_prop) continuous_const)
    let U : Set E := e.source ∩ e ⁻¹' V ∩ (range Q)ᶜ
    have hU : IsOpen U :=
      (e.isOpen_inter_preimage hV).inter (isCompact_range Q.continuous).isClosed.isOpen_compl
    have hpU : p ∈ U := by
      refine ⟨⟨hpe,?_⟩,hpQ⟩
      change 2*(u:ℝ)-1 < (e p) 1 ∧ (e p) 1 < 2*(w:ℝ)-1
      rw [hep]
      have hu' : (u:ℝ) < 1/2 := hum
      have hw' : 1/2 < (w:ℝ) := hmw
      constructor <;> simp only [PiLp.zero_apply] <;> linarith
    let E' := e.restrOpen U hU
    have hpE' : p ∈ E'.source := ⟨hpe,hpU⟩
    have hbaxis (x : E) (hx : x ∈ E'.source) : x ∈ b.image ↔ (e x) 0 = 0 := by
      have hxe : x ∈ e.source := hx.1
      have hxU : x ∈ U := hx.2
      have hbounds : 2*(u:ℝ)-1 < (e x) 1 ∧ (e x) 1 < 2*(w:ℝ)-1 := hxU.1.2
      rw [hb]
      constructor
      · rintro (⟨r,rfl⟩ | hxQ)
        · change (e (a (intervalAffine u w r))) 0 = 0
          rw [haCoord]
          rfl
        · exact (hxU.2 hxQ).elim
      · intro hx0
        left
        rw [hrangeA]
        let r : I := ⟨((e x) 1 + 1)/2,by
          have hu0 : 0 ≤ (u:ℝ) := u.property.1
          have hw1 : (w:ℝ) ≤ 1 := w.property.2
          constructor <;> linarith [hbounds.1,hbounds.2]⟩
        have hruw : r ∈ Icc u w := by
          constructor
          · change (u:ℝ) ≤ ((e x) 1 + 1)/2
            linarith [hbounds.1]
          · change ((e x) 1 + 1)/2 ≤ (w:ℝ)
            linarith [hbounds.2]
        refine ⟨r,hruw,?_⟩
        apply e.injOn (haE r) hxe
        rw [haCoord]
        ext i
        fin_cases i
        · exact hx0.symm
        · change 2*(((e x) 1+1)/2)-1 = (e x) 1
          ring
    let L : Plane ≃ₜ ℝ × ℝ :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let F := L.trans (Homeomorph.prodComm ℝ ℝ)
    let W : Set (ℝ × ℝ) := F '' E'.target
    let H : E'.source ≃ₜ W := E'.toHomeomorphSourceTarget.trans (F.image E'.target)
    refine ⟨E'.source,W,hpE',H,E'.open_source,F.isOpenMap _ E'.open_target,?_,?_⟩
    · change ((e p) 1,(e p) 0) = (0,0)
      rw [hep]
      rfl
    · intro x hx
      change (x ∈ c.image ↔ (e x) 1 = 0) ∧ (x ∈ b.image ↔ (e x) 0 = 0)
      exact ⟨haxis x hx.1,hbaxis x hx⟩
  have htrans : Transverse c b := ⟨hfinite,by
    intro x hx
    have hxp : x = p := by rw [hcrossSet] at hx; exact mem_singleton_iff.mp hx
    exact hxp ▸ hcross⟩
  refine ⟨b,htrans,?_⟩
  have hfinset : htrans.1.toFinset = {p} := by
    ext x
    simp only [Finite.mem_toFinset,Finset.mem_singleton]
    rw [hcrossSet,mem_singleton_iff]
  rw [hfinset]
  exact Finset.card_singleton p

end CurveComplex.Hyperbolic
