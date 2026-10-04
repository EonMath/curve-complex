import CurveComplexGenusTwo.Topology.ActualHarerComparisonDisk.ActualHarerComparisonDiskAssembly
import CurveComplexGenusTwo.Topology.ActualHarerNoncornerTangency.ActualHarerNoncornerTangency
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.VerifiedCarrierBridgeComponents
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import CurveComplexGenusTwo.Topology.ArcTrim.SupportedStrictDiskEnlargementStatement
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedSideEndpointMarks
import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.ModelCurve
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualStripSurfaceChart
import Mathlib.Topology.Order.IntermediateValue
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ClosedBallTailAvoidingEnlargement


open CurveComplex Set Topology Schoenflies

namespace ActualHarerWholeAnchorRail

private theorem disjoint_compact_anchor_family_constructs_whole_anchor_clear_strip
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {I : Type} [Finite I] (a : I → C(Interval,S))
    (ha : ∀ i, IsEmbedding (a i))
    (hdisjoint : ∀ i k, i ≠ k → Disjoint (range (a i)) (range (a k)))
    (i : I) :
    ∃ E : C(Interval × Set.Icc (-1:ℝ) 1,S),
      IsEmbedding E ∧
      (∀ t, E (t,⟨0,by norm_num⟩) = a i t) ∧
      (∀ k, k ≠ i → Disjoint (range E) (range (a k))) ∧
      ∀ (t : Interval) (w : Set.Icc (-1:ℝ) 1), (w : ℝ) ≠ 0 → E (t,w) ∉ ⋃ k,range (a k) := by
  classical
  let O : Set S := (⋃ k : {k : I // k≠i},range (a k.val))ᶜ
  have hO : IsOpen O := (isClosed_iUnion_of_finite
    (fun k : {k : I // k≠i} => (isCompact_range (a k.val).continuous).isClosed)).isOpen_compl
  have haiO : range (a i) ⊆ O := by
    intro y hy hother
    obtain ⟨k,hk⟩ := mem_iUnion.mp hother
    exact Set.disjoint_left.mp (hdisjoint i k.val k.property.symm) hy hk
  obtain ⟨E,hE,hcenter,hEO⟩ := source_whole_embedded_arc_strip (a i) (ha i) O hO haiO
  let Ec : C(Interval × Set.Icc (-1:ℝ) 1,S) := ⟨E,hE.continuous⟩
  have hOther : ∀ k,k≠i → Disjoint (range Ec) (range (a k)) := by
    intro k hki
    apply Set.disjoint_left.mpr
    intro y hy hyk
    exact hEO hy (mem_iUnion.mpr ⟨⟨k,hki⟩,hyk⟩)
  refine ⟨Ec,hE,hcenter,hOther,?_⟩
  intro t w hw hy
  obtain ⟨k,hk⟩ := mem_iUnion.mp hy
  by_cases hki : k=i
  · subst k
    obtain ⟨u,hu⟩ := hk
    have he : E (t,w)=E (u,⟨0,by norm_num⟩) := hu.symm.trans (hcenter u).symm
    exact hw (congrArg (fun z : Interval × Set.Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he))
  · exact Set.disjoint_left.mp (hOther k hki) (Set.mem_range_self (t,w)) hk

private theorem actual_disjoint_whole_moving_family_constructs_local_exact_axis_chart
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {J : Type} [Finite J] (b : J → C(Interval,S))
    (hb : ∀ j,IsEmbedding (b j))
    (hdisjoint : ∀ j k,j≠k → Disjoint (range (b j)) (range (b k)))
    (j : J) (s : Interval) (hs : s∈Ioo (0:Interval) 1)
    (U : Set S) (hU : IsOpen U) (hps : b j s∈U) :
    ∃ Q : OpenPartialHomeomorph S Plane,
      b j s∈Q.source ∧ Q.source⊆U ∧ Q (b j s)=Plane.mk s 0 ∧
      (∀ k,k≠j → Disjoint Q.source (range (b k))) ∧
      (∀ y∈Q.source,y∈range (b j) ↔ Q y 1=0) ∧
      ∀ K : Set Plane,
        ({y : S | y∈Q.source ∧ Q y∈K}∩range (b j))=
        {y : S | y∈Q.source ∧ Q y∈K ∧ Q y 1=0} := by
  obtain ⟨E,hE,hcenter,hOther,_⟩ :=
    disjoint_compact_anchor_family_constructs_whole_anchor_clear_strip b hb hdisjoint j
  obtain ⟨Q,hQs,_,hQcoord,hQaxis⟩ :=
    source_embedded_strip_interior_chart E hE (b j) hcenter
  have hpQ : b j s∈Q.source := by
    rw [hQs]
    exact ⟨(s,⟨0,by norm_num⟩),⟨hs.1,hs.2,by norm_num,by norm_num⟩,hcenter s⟩
  let N := Q.restr U
  have hNs : N.source=Q.source∩U := by
    change Q.source∩interior U=Q.source∩U
    rw [hU.interior_eq]
  have hNp : b j s∈N.source := by rw [hNs];exact ⟨hpQ,hps⟩
  have hNaxis : ∀ y∈N.source,y∈range (b j) ↔ N y 1=0 := by
    intro y hy
    exact hQaxis y (by rw [hNs] at hy;exact hy.1)
  refine ⟨N,hNp,?_,?_,?_,hNaxis,?_⟩
  · rw [hNs];exact inter_subset_right
  · change Q (b j s)=Plane.mk s 0
    rw [← hcenter s]
    exact hQcoord (s,⟨0,by norm_num⟩) hs.1 hs.2 (by norm_num) (by norm_num)
  · intro k hkj
    apply Set.disjoint_left.mpr
    intro y hy hyk
    have hyQ : y∈Q.source := by rw [hNs] at hy;exact hy.1
    have hyE : y∈range E := by
      rw [hQs] at hyQ
      exact image_subset_range E _ hyQ
    exact Set.disjoint_left.mp (hOther k hkj) hyE hyk
  · intro K
    ext y
    constructor
    · rintro ⟨⟨hy,hK⟩,hbj⟩
      exact ⟨hy,hK,(hNaxis y hy).mp hbj⟩
    · rintro ⟨hy,hK,haxis⟩
      exact ⟨⟨hy,hK⟩,(hNaxis y hy).mpr haxis⟩

private theorem horizontal_unit_square_axis_is_crosscut :
    let A : Set Plane := {z | z∈Plane.closedSquare 0 1 ∧ z 1=0}
    let u := Plane.mk (-1) 0
    let v := Plane.mk 1 0
    IsArcBetween A u v ∧ u∈modelCurve ∧ v∈modelCurve ∧
      A\{u,v}⊆Plane.openSquare 0 1 := by
  dsimp only
  let f : ℝ → Plane := fun t => Plane.mk (2*t-1) 0
  have hf : Continuous f := by dsimp [f];fun_prop
  have himg : f '' Set.Icc (0:ℝ) 1={z | z∈Plane.closedSquare 0 1 ∧ z 1=0} := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      constructor
      · apply mem_closedSquare_zero_one.mpr
        change max |2*t-1| |(0:ℝ)|≤1
        rw [max_le_iff,abs_le]
        exact ⟨⟨by linarith [ht.1],by linarith [ht.2]⟩,by norm_num⟩
      · rfl
    · rintro ⟨hz,hz1⟩
      have hz0 : |z 0|≤1 :=
        (le_max_left _ _).trans (mem_closedSquare_zero_one.mp hz)
      refine ⟨(z 0+1)/2,⟨by linarith [abs_le.mp hz0],by linarith [abs_le.mp hz0]⟩,?_⟩
      ext k
      fin_cases k
      · change 2*((z 0+1)/2)-1=z 0
        ring
      · exact hz1.symm
  refine ⟨⟨f,hf.continuousOn,?_,himg,by norm_num [f],by norm_num [f]⟩,?_,?_,?_⟩
  · intro t _ r _ h
    have h0 := congrArg (fun z:Plane => z 0) h
    change 2*t-1=2*r-1 at h0
    linarith
  · change max |(-1:ℝ)| |(0:ℝ)|=1
    norm_num
  · change max |(1:ℝ)| |(0:ℝ)|=1
    norm_num
  · rintro z ⟨⟨hz,hz1⟩,hne⟩
    have hz0 : |z 0|≤1 :=
      (le_max_left _ _).trans (mem_closedSquare_zero_one.mp hz)
    have hz0ne : |z 0|≠1 := by
      intro he
      rcases (abs_eq (show (0:ℝ)≤1 by norm_num)).mp he with he | he
      · apply hne
        right
        apply Set.mem_singleton_iff.mpr
        ext k
        fin_cases k <;> assumption
      · apply hne
        left
        ext k
        fin_cases k <;> assumption
    apply mem_openSquare_zero_one.mpr
    change max |z 0| |z 1|<1
    rw [max_lt_iff,hz1]
    exact ⟨lt_of_le_of_ne hz0 hz0ne,by norm_num⟩

end ActualHarerWholeAnchorRail

namespace ActualHarerContactSides

private theorem actual_isolated_whole_trace_contact_constructs_two_signed_branch_windows
    {S : Type} [TopologicalSpace S]
    (a b : C(Interval,S)) (ha : IsEmbedding a)
    (Q : OpenPartialHomeomorph S Plane)
    (haxis : ∀ y∈Q.source,y∈range b ↔ Q y 1=0)
    (s : Interval) (hs : s∈Ioo (0:Interval) 1)
    (hpQ : a s∈Q.source)
    (hisolated : Q.source∩(range a∩range b)={a s}) :
    ∃ l r : Interval,l<s ∧ s<r ∧
      (∀ t∈Icc l r,a t∈Q.source) ∧
      ((∀ t∈Ico l s,Q (a t) 1<0) ∨ (∀ t∈Ico l s,0<Q (a t) 1)) ∧
      ((∀ t∈Ioc s r,Q (a t) 1<0) ∨ (∀ t∈Ioc s r,0<Q (a t) 1)) := by
  have hn : a ⁻¹' Q.source∈nhds s := (Q.open_source.preimage a.continuous).mem_nhds hpQ
  obtain ⟨l₀,r₀,hs₀,hlocal⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0,hs.1⟩ ⟨1,hs.2⟩).mp hn
  obtain ⟨l,hl₀,hls⟩ := exists_between hs₀.1
  obtain ⟨r,hsr,hrr₀⟩ := exists_between hs₀.2
  have hin : ∀ t∈Icc l r,a t∈Q.source := by
    intro t ht
    exact hlocal ⟨hl₀.trans_le ht.1,ht.2.trans_lt hrr₀⟩
  let z : Interval → ℝ := fun t => Q (a t) 1
  have hzc : ContinuousOn z (Icc l r) :=
    (Plane.continuous_coord 1).continuousOn.comp
      (Q.continuousOn.comp a.continuous.continuousOn hin) (fun _ _ => Set.mem_univ _)
  have hnz : ∀ t∈Icc l r,t≠s → z t≠0 := by
    intro t ht hts hz
    have hbt : a t∈range b := (haxis _ (hin t ht)).mpr hz
    have he : a t=a s := by
      have hmem : a t∈Q.source∩(range a∩range b) :=
        ⟨hin t ht,Set.mem_range_self t,hbt⟩
      exact Set.mem_singleton_iff.mp (hisolated ▸ hmem)
    exact hts (ha.injective he)
  have hleft : ∀ t∈Ico l s,z t≠0 := by
    intro t ht
    exact hnz t ⟨ht.1,ht.2.le.trans hsr.le⟩ (ne_of_lt ht.2)
  have hright : ∀ t∈Ioc s r,z t≠0 := by
    intro t ht
    exact hnz t ⟨hls.le.trans ht.1.le,ht.2⟩ (ne_of_gt ht.1)
  have hzl : ContinuousOn z (Ico l s) := hzc.mono (fun t ht =>
    ⟨ht.1,ht.2.le.trans hsr.le⟩)
  have hzr : ContinuousOn z (Ioc s r) := hzc.mono (fun t ht =>
    ⟨hls.le.trans ht.1.le,ht.2⟩)
  refine ⟨l,r,hls,hsr,hin,?_,?_⟩
  · have hl : l∈Ico l s := ⟨le_refl _,hls⟩
    rcases lt_or_gt_of_ne (hleft l hl) with hneg | hpos
    · exact Or.inl (fun t ht => isPreconnected_Ico.gt_of_ne hzl hleft ⟨l,hl,hneg⟩ ht)
    · exact Or.inr (fun t ht => isPreconnected_Ico.lt_of_ne hzl hleft ⟨l,hl,hpos⟩ ht)
  · have hr : r∈Ioc s r := ⟨hsr,le_refl _⟩
    rcases lt_or_gt_of_ne (hright r hr) with hneg | hpos
    · exact Or.inl (fun t ht => isPreconnected_Ioc.gt_of_ne hzr hright ⟨r,hr,hneg⟩ ht)
    · exact Or.inr (fun t ht => isPreconnected_Ioc.lt_of_ne hzr hright ⟨r,hr,hpos⟩ ht)

private theorem actual_parabolic_unit_square_bypass_crosscut
    (ε : ℝ) (hε : ε≠0) (hε1 : |ε|≤1) :
    ∃ B : Set Plane,
      IsArcBetween B (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
      B\{Plane.mk (-1) 0,Plane.mk 1 0}⊆Plane.openSquare 0 1 ∧
      (0 : Plane)∉B ∧
      ∀ z∈B\{Plane.mk (-1) 0,Plane.mk 1 0},0<ε*(z 1) := by
  let f : ℝ → Plane := fun t => Plane.mk (2*t-1) (ε*t*(1-t))
  let B : Set Plane := f '' Icc (0:ℝ) 1
  have hf : Continuous f := by dsimp [f];fun_prop
  have hf0 : f 0=Plane.mk (-1) 0 := by simp [f]
  have hf1 : f 1=Plane.mk 1 0 := by norm_num [f]
  have htInterior (t : ℝ) (ht : t∈Icc (0:ℝ) 1)
      (hnot : f t∉({Plane.mk (-1) 0,Plane.mk 1 0} : Set Plane)) : 0<t ∧ t<1 := by
    constructor
    · apply lt_of_le_of_ne ht.1
      intro he
      exact hnot (Or.inl (by rw [← he,hf0]))
    · apply lt_of_le_of_ne ht.2
      intro he
      exact hnot (Or.inr (by rw [he,hf1]; exact Set.mem_singleton _))
  refine ⟨B,⟨f,hf.continuousOn,?_,rfl,hf0,hf1⟩,?_,?_,?_⟩
  · intro t _ u _ he
    have he0 := congrArg (fun z:Plane => z 0) he
    change 2*t-1=2*u-1 at he0
    linarith
  · rintro z ⟨⟨t,ht,rfl⟩,hne⟩
    obtain ⟨ht0,ht1⟩ := htInterior t ht hne
    apply mem_openSquare_zero_one.mpr
    change max |2*t-1| |ε*t*(1-t)|<1
    rw [max_lt_iff,abs_lt]
    refine ⟨⟨by linarith,by linarith⟩,?_⟩
    have hy : |ε*t*(1-t)|=|ε| *(t*(1-t)) := by
      rw [abs_mul,abs_mul,abs_of_pos ht0,abs_of_pos (by linarith : 0<1-t)]
      ring
    rw [hy]
    have hmul : 0≤t*(1-t) := mul_nonneg ht0.le (by linarith)
    have hbound := mul_le_mul_of_nonneg_right hε1 hmul
    nlinarith [sq_nonneg (t-1/2)]
  · rintro ⟨t,ht,he⟩
    have he0 := congrArg (fun z:Plane => z 0) he
    have he1 := congrArg (fun z:Plane => z 1) he
    change 2*t-1=0 at he0
    change ε*t*(1-t)=0 at he1
    have htHalf : t=1/2 := by linarith
    rw [htHalf] at he1
    exact hε (by linarith)
  · rintro z ⟨⟨t,ht,rfl⟩,hne⟩
    obtain ⟨ht0,ht1⟩ := htInterior t ht hne
    change 0<ε*(ε*t*(1-t))
    have hsq : 0<ε*ε := mul_self_pos.mpr hε
    have hprod : 0<(ε*ε)*t*(1-t) := mul_pos (mul_pos hsq ht0) (by linarith)
    nlinarith only [hprod]

private theorem actual_same_signed_local_branches_construct_whole_trace_one_side_chart_restriction
    {S : Type} [TopologicalSpace S] [T2Space S]
    (a : C(Interval,S)) (ha : IsEmbedding a)
    (Q : OpenPartialHomeomorph S Plane) (s l r : Interval)
    (hls : l<s) (hsr : s<r) (hpQ : a s∈Q.source)
    (hpAxis : Q (a s) 1=0) (ε : ℝ)
    (hside : ∀ t∈Ioo l r,t≠s → ε*Q (a t) 1<0) :
    ∃ N : OpenPartialHomeomorph S Plane,
      a s∈N.source ∧ N.source⊆Q.source ∧ (∀ y,N y=Q y) ∧
      ∀ y∈N.source,y∈range a → ε*N y 1≤0 := by
  let Far : Set S := a '' (Ioo l r)ᶜ
  have hFar : IsClosed Far := ((isCompact_univ.of_isClosed_subset
    isOpen_Ioo.isClosed_compl (Set.subset_univ _)).image a.continuous).isClosed
  have hpFar : a s∉Far := by
    rintro ⟨t,ht,he⟩
    have htEq : t=s := ha.injective he
    exact ht (htEq.symm ▸ ⟨hls,hsr⟩)
  let N := Q.restr Farᶜ
  have hNs : N.source=Q.source∩Farᶜ := by
    change Q.source∩interior Farᶜ=Q.source∩Farᶜ
    rw [hFar.isOpen_compl.interior_eq]
  refine ⟨N,?_,?_,fun _ => rfl,?_⟩
  · rw [hNs];exact ⟨hpQ,hpFar⟩
  · rw [hNs];exact inter_subset_left
  · intro y hy
    rintro ⟨t,rfl⟩
    have hyFar : a t∉Far := by rw [hNs] at hy;exact hy.2
    have htLocal : t∈Ioo l r := by
      by_contra hn
      exact hyFar ⟨t,hn,rfl⟩
    change ε*Q (a t) 1≤0
    by_cases htEq : t=s
    · rw [htEq,hpAxis,mul_zero]
    · exact (hside t htLocal htEq).le

private theorem actual_axis_chart_closed_square_normalization_preserves_transverse_halfplanes
    {S : Type} [TopologicalSpace S]
    (Q : OpenPartialHomeomorph S Plane) (p : S) (hp : p∈Q.source)
    (hc : Q p 1=0) :
    ∃ N : OpenPartialHomeomorph S Plane,
      N.source=Q.source ∧ N p=0 ∧ Plane.closedSquare 0 1⊆N.target ∧
      (∀ y,N y 1=0 ↔ Q y 1=0) ∧
      ∀ ε y,ε*N y 1≤0 ↔ ε*Q y 1≤0 := by
  let f : ℝ × Plane → Plane := fun z => z.1 • z.2+Q p
  have hf : Continuous f := by dsimp [f];fun_prop
  have hprod : ({0} : Set ℝ) ×ˢ Plane.closedSquare 0 1⊆f ⁻¹' Q.target := by
    rintro ⟨t,z⟩ ⟨ht,_⟩
    have ht0 : t=0 := ht
    subst t
    simpa [f] using Q.map_source hp
  obtain ⟨V,W,hV,_,h0V,hKW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedSquare 0 1)
      (Q.open_target.preimage hf) hprod
  obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (Set.mem_singleton 0))
  let δ := ε/2
  have hδ : 0<δ := by dsimp [δ];linarith
  have hδne : δ≠0 := ne_of_gt hδ
  have hδV : δ∈V := hεV (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hδ]
    dsimp [δ];linarith)
  let H : Plane ≃ₜ Plane := (Homeomorph.subRight (Q p)).trans
    (Homeomorph.smulOfNeZero δ hδne).symm
  let N := Q.trans H.toOpenPartialHomeomorph
  have hNs : N.source=Q.source := by simp [N,OpenPartialHomeomorph.trans_source]
  have hNval (y : S) : N y=δ⁻¹ • (Q y-Q p) := rfl
  have hHinv (z : Plane) : H.symm z=δ • z+Q p := rfl
  have hcoord (y : S) : N y 1=δ⁻¹*(Q y 1) := by
    rw [hNval,PiLp.smul_apply,Plane.sub_apply,hc,sub_zero]
    rfl
  refine ⟨N,hNs,?_,?_,?_,?_⟩
  · rw [hNval,sub_self,smul_zero]
  · intro z hz
    have htarget : H.symm z∈Q.target := by
      rw [hHinv]
      exact hVW (show (δ,z)∈V ×ˢ W from ⟨hδV,hKW hz⟩)
    simpa [N,OpenPartialHomeomorph.trans_target] using htarget
  · intro y
    rw [hcoord]
    simp [hδne]
  · intro ε y
    rw [hcoord]
    have heq : ε*(δ⁻¹*Q y 1)=δ⁻¹*(ε*Q y 1) := by ring
    rw [heq]
    constructor
    · intro h
      by_contra hn
      have hpos : 0<ε*Q y 1 := lt_of_not_ge hn
      have hprod := mul_pos (inv_pos.mpr hδ) hpos
      linarith
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hδ).le h

end ActualHarerContactSides

namespace ActualHarerWholeGraph

private theorem actual_disjoint_finite_arc_families_corner_constructs_other_labels_clear_open_neighborhood
    (S : Type) [TopologicalSpace S] [T2Space S]
    (I J : Type) [Finite I] [Finite J]
    (a : I → C(Interval,S)) (b : J → C(Interval,S))
    (ha : ∀ i k,i≠k → Disjoint (Set.range (a i)) (Set.range (a k)))
    (hb : ∀ j k,j≠k → Disjoint (Set.range (b j)) (Set.range (b k)))
    (i : I) (j : J) (p : S)
    (hpa : p∈Set.range (a i)) (hpb : p∈Set.range (b j))
    (V : Set S) (hV : IsOpen V) (hpV : p∈V) :
    ∃ U : Set S, IsOpen U ∧ p∈U ∧ U⊆V ∧
      (∀ k,k≠i → Disjoint U (Set.range (a k))) ∧
      (∀ k,k≠j → Disjoint U (Set.range (b k))) := by
  classical
  let A : Set S := ⋃ k : {k : I // k≠i},Set.range (a k.val)
  let B : Set S := ⋃ k : {k : J // k≠j},Set.range (b k.val)
  have hAc : IsClosed A := isClosed_iUnion_of_finite
    (fun k : {k : I // k≠i} => (isCompact_range (a k.val).continuous).isClosed)
  have hBc : IsClosed B := isClosed_iUnion_of_finite
    (fun k : {k : J // k≠j} => (isCompact_range (b k.val).continuous).isClosed)
  have hpA : p∉A := by
    intro hp
    obtain ⟨k,hk⟩ := mem_iUnion.mp hp
    exact Set.disjoint_left.mp (ha i k.val (Ne.symm k.property)) hpa hk
  have hpB : p∉B := by
    intro hp
    obtain ⟨k,hk⟩ := mem_iUnion.mp hp
    exact Set.disjoint_left.mp (hb j k.val (Ne.symm k.property)) hpb hk
  refine ⟨V∩(A∪B)ᶜ,hV.inter (hAc.union hBc).isOpen_compl,
    ⟨hpV,fun hp => hp.elim hpA hpB⟩,inter_subset_left,?_,?_⟩
  · intro k hki
    apply Set.disjoint_left.mpr
    intro x hx hxk
    exact hx.2 (Or.inl (mem_iUnion.mpr ⟨⟨k,hki⟩,hxk⟩))
  · intro k hkj
    apply Set.disjoint_left.mpr
    intro x hx hxk
    exact hx.2 (Or.inr (mem_iUnion.mpr ⟨⟨k,hkj⟩,hxk⟩))

private theorem actual_finite_whole_graph_genuine_contact_constructs_isolated_clear_open_neighborhood
    {S : Type} [TopologicalSpace S] [T2Space S]
    {I J : Type} [Finite I] [Finite J]
    (a : I → C(Interval,S)) (b : J → C(Interval,S))
    (ha : ∀ i k,i≠k → Disjoint (Set.range (a i)) (Set.range (a k)))
    (hb : ∀ j k,j≠k → Disjoint (Set.range (b j)) (Set.range (b k)))
    (hfinite : ((⋃ i,Set.range (a i))∩⋃ j,Set.range (b j)).Finite)
    (F : Set S) (i : I) (j : J) (p : S)
    (hpa : p∈Set.range (a i)) (hpb : p∈Set.range (b j))
    (hpF : p∈F) (hpFront : p∉frontier F) :
    ∃ U : Set S,IsOpen U ∧ p∈U ∧ U⊆interior F ∧
      (∀ k,k≠i → Disjoint U (Set.range (a k))) ∧
      (∀ k,k≠j → Disjoint U (Set.range (b k))) ∧
      U∩((⋃ k,Set.range (a k))∩⋃ k,Set.range (b k))={p} := by
  classical
  let C : Set S := (⋃ k,Set.range (a k))∩⋃ k,Set.range (b k)
  have hpC : p∈C := ⟨mem_iUnion.mpr ⟨i,hpa⟩,mem_iUnion.mpr ⟨j,hpb⟩⟩
  have hpInt : p∈interior F := by
    by_contra hn
    exact hpFront ((mem_frontier_iff_notMem_interior hpF).mpr hn)
  let V : Set S := interior F∩(C\{p})ᶜ
  have hV : IsOpen V := isOpen_interior.inter
    (hfinite.diff (t := {p})).isClosed.isOpen_compl
  have hpV : p∈V := ⟨hpInt,fun hp => hp.2 (Set.mem_singleton p)⟩
  obtain ⟨U,hU,hpU,hUV,hUa,hUb⟩ :=
    actual_disjoint_finite_arc_families_corner_constructs_other_labels_clear_open_neighborhood
      S I J a b ha hb i j p hpa hpb V hV hpV
  refine ⟨U,hU,hpU,fun y hy => (hUV hy).1,hUa,hUb,?_⟩
  ext y
  constructor
  · rintro ⟨hyU,hyC⟩
    have hyNot : y∉C\{p} := (hUV hyU).2
    by_contra hyn
    exact hyNot ⟨hyC,hyn⟩
  · intro hy
    have hyp : y=p := hy
    subst y
    exact ⟨hpU,hpC⟩

end ActualHarerWholeGraph

namespace ActualHarerSupportedBypass

private theorem embedded_surface_disk_frontier_eq_boundary_image
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) :
    frontier (Set.range d) =
      d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
  rw [hclosed.frontier_eq,
    CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, hxnot⟩
    refine ⟨x, ?_, rfl⟩
    have hxle : dist x.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := x.property
    have hxge : 1 ≤ dist x.val (0 : EuclideanSpace ℝ (Fin 2)) := by
      by_contra hn
      apply hxnot
      exact ⟨x, lt_of_not_ge hn, rfl⟩
    exact le_antisymm hxle hxge
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    have hxy := hd.injective he
    subst y
    change dist x.val (0 : EuclideanSpace ℝ (Fin 2)) < 1 at hy
    change dist x.val (0 : EuclideanSpace ℝ (Fin 2)) = 1 at hx
    linarith

private theorem actual_negative_local_tangency_constructs_normalized_whole_anchor_side_chart
    {S : Type} [TopologicalSpace S] [T2Space S] (F : Set S)
    {I J : Type} (a : I → C(Interval, ↥F)) (b : J → C(Interval, ↥F))
    (i : I) (j : J) (c : C(Interval,S))
    (hc : ∀ t, c t = (a i t).val) (hemb : IsEmbedding c)
    (Q : OpenPartialHomeomorph S Plane)
    (hF : Q.source ⊆ interior F)
    (haxis : ∀ y : ↥F, y.val ∈ Q.source → (y ∈ range (b j) ↔ Q y.val 1=0))
    (hotherA : ∀ k, k ≠ i → ∀ y ∈ range (a k), y.val ∉ Q.source)
    (hotherB : ∀ k, k ≠ j → ∀ y ∈ range (b k), y.val ∉ Q.source)
    (s l r : Interval) (hls : l<s) (hsr : s<r)
    (hp : c s ∈ Q.source) (hz : Q (c s) 1=0)
    (ε : ℝ) (hside : ∀ t∈Ioo l r, t≠s → ε*Q (c t) 1<0) :
    ∃ E : OpenPartialHomeomorph S Plane,
      c s∈E.source ∧ E (c s)=0 ∧ Plane.closedSquare 0 1⊆E.target ∧
      E.source⊆interior F ∧
      (∀ y:↥F,y.val∈E.source → (y∈range (b j) ↔ E y.val 1=0)) ∧
      (∀ y:↥F,y.val∈E.source → y∈(⋃ k,range (a k)) → ε*E y.val 1≤0) ∧
      (∀ k,k≠j → ∀ y∈range (b k),y.val∉E.source) := by
  have hsign := hside
  obtain ⟨N,hpN,hNQ,hval,hlocal⟩ :=
    ActualHarerContactSides.actual_same_signed_local_branches_construct_whole_trace_one_side_chart_restriction
      c hemb Q s l r hls hsr hp hz ε hsign
  have hNzero : N (c s) 1=0 := by rw [hval];exact hz
  obtain ⟨E,hEN,hE0,hSquare,hzero,hsigns⟩ :=
    ActualHarerContactSides.actual_axis_chart_closed_square_normalization_preserves_transverse_halfplanes
      N (c s) hpN hNzero
  have hEQ : E.source⊆Q.source := by rw [hEN];exact hNQ
  refine ⟨E,hEN.symm ▸ hpN,hE0,hSquare,hEQ.trans hF,?_,?_,?_⟩
  · intro y hy
    have hzEquiv : E y.val 1=0 ↔ Q y.val 1=0 := by
      rw [hzero,hval]
    exact (haxis y (hEQ hy)).trans hzEquiv.symm
  · intro y hy hyA
    obtain ⟨k,t,ht⟩ := mem_iUnion.mp hyA
    by_cases hki : k=i
    · subst k
      have hyc : y.val∈range c := by
        refine ⟨t,?_⟩
        rw [hc,ht]
      have hnonpos := hlocal y.val (hEN ▸ hy) hyc
      have hnorm := (hsigns ε y.val).mpr hnonpos
      exact hnorm
    · exact (hotherA k hki y ⟨t,ht⟩ (hEQ hy)).elim
  · intro k hk y hy hyE
    exact hotherB k hk y hy (hEQ hyE)

private theorem actual_normalized_opposite_whole_anchor_chart_assembles_supported_crosscuts
    {S : Type} [TopologicalSpace S] (F : Set S)
    {I J : Type} (a : I → C(Interval, ↥F)) (b : J → C(Interval, ↥F))
    (j : J) (E : OpenPartialHomeomorph S Plane)
    (hSquare : Plane.closedSquare 0 1 ⊆ E.target)
    (hF : E.source ⊆ interior F)
    (haxis : ∀ y : ↥F, y.val ∈ E.source →
      (y ∈ Set.range (b j) ↔ E y.val 1 = 0))
    (ε : ℝ) (hε : ε≠0) (hε1 : |ε|≤1)
    (hside : ∀ y : ↥F, y.val ∈ E.source →
      y ∈ (⋃ k, Set.range (a k)) → ε*E y.val 1 ≤ 0)
    (hothers : ∀ k, k ≠ j → ∀ y ∈ Set.range (b k), y.val ∉ E.source)
    (p : ↥F) (hpS : p.val ∈ E.source) (hp0 : E p.val = 0)
    (hpA : p ∈ ⋃ k, Set.range (a k)) :
    ∃ (A B : Set Plane) (u v : Plane),
      IsArcBetween A u v ∧ IsArcBetween B u v ∧
      u ∈ modelCurve ∧ v ∈ modelCurve ∧
      A \ {u,v} ⊆ Plane.openSquare 0 1 ∧
      B \ {u,v} ⊆ Plane.openSquare 0 1 ∧
      {y : S | y ∈ E.source ∧ E y ∈ Plane.openSquare 0 1} ⊆ interior F ∧
      {z : S | z ∈ E.source ∧ E z ∈ A} ⊆ F ∧
      ({y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ Plane.closedSquare 0 1}} ∩
        Set.range (b j) = {y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ A}}) ∧
      ({y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ B}} ∩
        (⋃ k, Set.range (a k)) ⊆ (⋃ k, Set.range (b k)) ∩ (⋃ k, Set.range (a k))) ∧
      (∃ p : ↥F, p ∈ {y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ A}} ∩
        (⋃ k, Set.range (a k)) ∧
        p ∉ {y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ B}}) ∧
      (∀ k, k ≠ j → ∀ y ∈ Set.range (b k),
        y.val ∉ {z : S | z ∈ E.source ∧ E z ∈ Plane.openSquare 0 1}) := by
  let A : Set Plane := {z | z ∈ Plane.closedSquare 0 1 ∧ z 1 = 0}
  have hends : ∀ y : ↥F, y.val ∈ E.source →
      E y.val ∈ ({Plane.mk (-1) 0, Plane.mk 1 0} : Set Plane) →
      y ∈ ⋃ k, Set.range (b k) := by
    intro y hy he
    apply mem_iUnion.mpr
    refine ⟨j, (haxis y hy).mpr ?_⟩
    rcases he with he | he
    · rw [he]; rfl
    · rw [Set.mem_singleton_iff.mp he]; rfl
  obtain ⟨B,hB,hBi,hpB,hSign⟩ :=
    ActualHarerContactSides.actual_parabolic_unit_square_bypass_crosscut ε hε hε1
  have hretain : {y:↥F | y.val∈E.source ∧ E y.val∈B}∩(⋃ k,range (a k))⊆
      (⋃ k,range (b k))∩(⋃ k,range (a k)) := by
    rintro y ⟨⟨hyE,hyB⟩,hyA⟩
    have hyEnds : E y.val∈({Plane.mk (-1) 0,Plane.mk 1 0} : Set Plane) := by
      by_contra hn
      have hpos := hSign (E y.val) ⟨hyB,hn⟩
      have hneg := hside y hyE hyA
      linarith
    exact ⟨hends y hyE hyEnds,hyA⟩
  have homit : p∉{y:↥F | y.val∈E.source ∧ E y.val∈B} := by
    rintro ⟨_,hpIn⟩
    rw [hp0] at hpIn
    exact hpB hpIn
  obtain ⟨hA,hu,hv,hAi⟩ := ActualHarerWholeAnchorRail.horizontal_unit_square_axis_is_crosscut
  refine ⟨A,B,Plane.mk (-1) 0,Plane.mk 1 0,hA,hB,hu,hv,hAi,hBi,?_,?_,?_,hretain,?_,?_⟩
  · intro y hy
    exact hF hy.1
  · intro y hy
    exact interior_subset (hF hy.1)
  · ext y
    constructor
    · rintro ⟨⟨hy,hK⟩,hyb⟩
      exact ⟨hy,hK,(haxis y hy).mp hyb⟩
    · rintro ⟨hy,hK,hz⟩
      exact ⟨⟨hy,hK⟩,(haxis y hy).mpr hz⟩
  · refine ⟨p,⟨⟨hpS,?_,?_⟩,hpA⟩,homit⟩
    · rw [hp0]
      exact mem_closedSquare_zero_one.mpr (by change max |(0:ℝ)| |(0:ℝ)| ≤ 1; norm_num)
    · rw [hp0]; rfl
  · intro k hk y hy
    rintro ⟨hyS,_⟩
    exact hothers k hk y hy hyS

private theorem embedded_disk_interior_chart {S : Type} [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (e : C(Metric.closedBall (0 : Plane) 1,S)) (he : IsEmbedding e) :
    ∃ F : OpenPartialHomeomorph S Plane,
      F.source = interior (range e) ∧ F.target = Metric.ball (0 : Plane) 1 ∧
      ∀ z (hz : z ∈ Metric.ball (0 : Plane) 1),
        F.symm z = e ⟨z,Metric.ball_subset_closedBall hz⟩ := by
  classical
  let B := Metric.ball (0 : Plane) 1
  let incl : B → Metric.closedBall (0 : Plane) 1 :=
    fun z => ⟨z.val,Metric.ball_subset_closedBall z.property⟩
  have hi : IsEmbedding incl :=
    Topology.IsEmbedding.subtypeVal.codRestrict _ _
  let f : B → S := e ∘ incl
  have hf : IsEmbedding f := he.comp hi
  have hr : range f = interior (range e) := by
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq e he]
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨incl z,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z.val,hz⟩,rfl⟩
  have hfo : IsOpenEmbedding f := ⟨hf,hr.symm ▸ isOpen_interior⟩
  letI : Nonempty B := ⟨⟨0,by simp [B]⟩⟩
  let G := hfo.toOpenPartialHomeomorph f
  let J := (Metric.isOpen_ball : IsOpen B).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : B → Plane)
  let F := G.symm.trans J
  have hFs : F.source = interior (range e) := by
    simp only [F,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
      G,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
      J,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
    exact hr
  have hFt : F.target = B := by
    simp only [F,OpenPartialHomeomorph.trans_target,OpenPartialHomeomorph.symm_target,
      G,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      J,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,preimage_univ,inter_univ, Subtype.range_val]
  refine ⟨F,hFs,hFt,?_⟩
  intro z hz
  change G (J.symm z) = _
  change f (J.symm z) = _
  have hJt : J.target = B := by simp [J]
  have hj : (J.symm z).val = z := J.right_inv (hJt.symm ▸ hz)
  change e (incl (J.symm z)) = _
  congr 1
  exact Subtype.ext hj

private theorem actual_embedded_closed_disk_constructs_containing_ambient_chart
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d) :
    ∃ Q : OpenPartialHomeomorph S Plane,
      range d⊆Q.source ∧ Q.target=Metric.ball (0:Plane) 1 := by
  obtain ⟨_,e,he,hde,_,_,_,_⟩ :=
    CurveComplex.LocalSurgery.exists_supported_strict_disk_enlargement
      d hd univ isOpen_univ (subset_univ _)
  obtain ⟨Q,hQsource,hQtarget,_⟩ := embedded_disk_interior_chart e he
  exact ⟨Q,hQsource.symm ▸ hde,hQtarget⟩

private theorem actual_embedded_closed_disk_constructs_full_plane_ambient_chart
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d) :
    ∃ E : OpenPartialHomeomorph S Plane,range d⊆E.source ∧ E.target=univ := by
  obtain ⟨Q,hDQ,hQt⟩ := actual_embedded_closed_disk_constructs_containing_ambient_chart d hd
  let H : OpenPartialHomeomorph Plane Plane := OpenPartialHomeomorph.univUnitBall
  let E := Q.trans H.symm
  have hEs : E.source=Q.source := by
    ext x
    simp only [E,OpenPartialHomeomorph.trans_source,mem_inter_iff,mem_preimage]
    constructor
    · exact fun h => h.1
    · intro hx
      refine ⟨hx,?_⟩
      change Q x∈Metric.ball (0:Plane) 1
      exact hQt ▸ Q.map_source hx
  have hEt : E.target=univ := by
    ext z
    simp only [E,OpenPartialHomeomorph.trans_target,mem_inter_iff,mem_preimage]
    constructor
    · intro _;exact mem_univ z
    · intro _
      refine ⟨mem_univ z,?_⟩
      change H z∈Q.target
      rw [hQt]
      exact H.map_source (mem_univ z)
  exact ⟨E,hEs.symm ▸ hDQ,hEt⟩

theorem actual_empty_whole_arc_graph_disk_constructs_supported_replacement_crosscut
    (S : Type) [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (I J : Type) [Finite I] [Finite J]
    (a : I → C(Interval, ↥F)) (b : J → C(Interval, ↥F))
    (ha : ∀ i, IsEmbedding (a i))
    (hb : ∀ j, IsEmbedding (b j))
    (hadisjoint : ∀ i k, i ≠ k →
      Disjoint (Set.range (a i)) (Set.range (a k)))
    (hbdisjoint : ∀ j k, j ≠ k →
      Disjoint (Set.range (b j)) (Set.range (b k)))
    (hfinite : ((⋃ i, Set.range (a i)) ∩ (⋃ j, Set.range (b j))).Finite)
    (ha0 : ∀ i, (a i 0).val ∈ frontier F)
    (ha1 : ∀ i, (a i 1).val ∈ frontier F)
    (hb0 : ∀ j, (b j 0).val ∈ frontier F)
    (hb1 : ∀ j, (b j 1).val ∈ frontier F)
    (haClear : ∀ i t, t ∈ Set.Ioo (0 : Interval) 1 →
      (a i t).val ∉ frontier F)
    (hbClear : ∀ j t, t ∈ Set.Ioo (0 : Interval) 1 →
      (b j t).val ∉ frontier F)
    (i : I) (j : J) (q g : C(Interval, S))
    (hq : IsEmbedding q) (hg : IsEmbedding g)
    (hqa : Set.range q ⊆ Set.range (fun t : Interval => (a i t).val))
    (hgb : Set.range g ⊆ Set.range (fun t : Interval => (b j t).val))
    (hzero : q 0 = g 0) (hone : q 1 = g 1)
    (d : C(Metric.closedBall (0 : Plane) 1, S))
    (hd : IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      Set.range q ∪ Set.range g)
    (hdF : Set.range d ⊆ F)
    (hempty : Disjoint (d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
      ((⋃ k, Set.range (fun t : Interval => (a k t).val)) ∪
        (⋃ k, Set.range (fun t : Interval => (b k t).val))))
    (hgenuine : q 0 ∉ frontier F ∨ q 1 ∉ frontier F) :
    ∃ (r : J) (E : OpenPartialHomeomorph S Plane)
      (A B : Set Plane) (u v : Plane),
      Plane.closedSquare 0 1 ⊆ E.target ∧
      IsArcBetween A u v ∧ IsArcBetween B u v ∧
      u ∈ modelCurve ∧ v ∈ modelCurve ∧
      A \ {u, v} ⊆ Plane.openSquare 0 1 ∧
      B \ {u, v} ⊆ Plane.openSquare 0 1 ∧
      {y : S | y ∈ E.source ∧ E y ∈ Plane.openSquare 0 1} ⊆ interior F ∧
      {z : S | z ∈ E.source ∧ E z ∈ A} ⊆ F ∧
      ({y : ↥F | y.val ∈ {z : S |
          z ∈ E.source ∧ E z ∈ Plane.closedSquare 0 1}} ∩ Set.range (b r) =
        {y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ A}}) ∧
      ({y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ B}} ∩
        (⋃ k, Set.range (a k)) ⊆
        (⋃ k, Set.range (b k)) ∩ (⋃ k, Set.range (a k))) ∧
      (∃ p : ↥F,
        p ∈ {y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ A}} ∩
          (⋃ k, Set.range (a k)) ∧
        p ∉ {y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧ E z ∈ B}}) ∧
      (∀ k, k ≠ r → ∀ y ∈ Set.range (b k),
        y.val ∉ {z : S | z ∈ E.source ∧ E z ∈ Plane.openSquare 0 1}) := by
  classical
  by_contra hNot
  have hTangencyFalse
      (k:I) (r:J) (s l h:Interval) (Q:OpenPartialHomeomorph S Plane) (ε:ℝ)
      (hε:ε=(-1:ℝ) ∨ ε=1)
      (hls:l<s) (hsh:s<h)
      (hp:(a k s).val∈Q.source) (hz:Q (a k s).val 1=0)
      (hQF:Q.source⊆interior F)
      (haxis:∀ y:↥F,y.val∈Q.source → (y∈range (b r) ↔ Q y.val 1=0))
      (hotherA:∀ k',k'≠k → ∀ y∈range (a k'),y.val∉Q.source)
      (hotherB:∀ r',r'≠r → ∀ y∈range (b r'),y.val∉Q.source)
      (hside:∀ w∈Ioo l h,w≠s → ε*Q (a k w).val 1<0) : False := by
    let c:C(Interval,S) := ⟨fun w=>(a k w).val,continuous_subtype_val.comp (a k).continuous⟩
    have hc:IsEmbedding c := IsEmbedding.subtypeVal.comp (ha k)
    obtain ⟨E,hpE,hE0,hSquare,hEF,hEaxis,hEside,hEother⟩ :=
      actual_negative_local_tangency_constructs_normalized_whole_anchor_side_chart
        F a b k r c (fun _=>rfl) hc Q hQF haxis hotherA hotherB s l h hls hsh hp hz ε hside
    have hε0:ε≠0 := by rcases hε with rfl|rfl <;> norm_num
    have hε1:|ε|≤1 := by rcases hε with rfl|rfl <;> norm_num
    obtain ⟨A,B,u,v,hout⟩ :=
      actual_normalized_opposite_whole_anchor_chart_assembles_supported_crosscuts
        F a b r E hSquare hEF hEaxis ε hε0 hε1 hEside hEother (a k s) hpE hE0
        (mem_iUnion.mpr ⟨k,mem_range_self s⟩)
    exact hNot ⟨r,E,A,B,u,v,hSquare,hout⟩
  have hNoNoncorner : ∀ x∈range d,x∈⋃ k,range (fun t:Interval=>(a k t).val) →
      x∈⋃ k,range (fun t:Interval=>(b k t).val) → x∈({q 0,q 1}:Set S) := by
    intro x hxD hxA hxB
    by_contra hx
    obtain ⟨k,r,s,t,l,h,Q,ε,hs,ht,has,hbt,hls,hsh,hε,hp,hz,hQF,haxis,hotherA,hotherB,hwin,hside⟩ :=
      actual_empty_whole_graph_disk_noncorner_contact_constructs_tangency_window
        S F I J a b ha hb hadisjoint hbdisjoint hfinite ha0 ha1 hb0 hb1 haClear hbClear
        i j q g hq hg hqa hgb hzero hone d hd hboundary hdF hempty hgenuine x hxD hxA hxB hx
    apply hTangencyFalse k r s l h Q ε hε hls hsh
    · exact has ▸ hp
    · exact has ▸ hz
    · exact hQF
    · exact haxis
    · exact hotherA
    · exact hotherB
    · exact hside
  have hCornerCross : ∀ v:Interval,(v=0 ∨ v=1) → q v∉frontier F →
      ∃ s t l h:Interval,∃ Q:OpenPartialHomeomorph S Plane,∃ ε:ℝ,
      s∈Ioo (0:Interval) 1 ∧ t∈Ioo (0:Interval) 1 ∧
      (a i s).val=q v ∧ (b j t).val=q v ∧ l<s ∧ s<h ∧
      (ε=(-1:ℝ) ∨ ε=1) ∧ q v∈Q.source ∧ Q.source⊆interior F ∧
      (∀ y:↥F,y.val∈Q.source → (y∈range (b j) ↔ Q y.val 1=0)) ∧
      (∀ w∈Icc l h,(a i w).val∈Q.source) ∧
      (∀ w∈Ico l s,ε*Q (a i w).val 1<0) ∧
      (∀ w∈Ioc s h,0<ε*Q (a i w).val 1) := by
    intro v hv hvFront
    have hqg : q v=g v := by
      rcases hv with rfl | rfl
      · exact hzero
      · exact hone
    obtain ⟨s,hs⟩ := hqa (Set.mem_range_self v)
    obtain ⟨t,ht⟩ := hgb (show q v∈range g from ⟨v,hqg.symm⟩)
    have hs0 : s≠0 := by
      intro he
      exact hvFront (hs ▸ he ▸ ha0 i)
    have hs1 : s≠1 := by
      intro he
      exact hvFront (hs ▸ he ▸ ha1 i)
    have ht0 : t≠0 := by
      intro he
      exact hvFront (ht ▸ he ▸ hb0 j)
    have ht1 : t≠1 := by
      intro he
      exact hvFront (ht ▸ he ▸ hb1 j)
    have hsInterior : s∈Ioo (0:Interval) 1 :=
      ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),lt_of_le_of_ne s.property.2 hs1⟩
    have htInterior : t∈Ioo (0:Interval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
    have hcontact : (a i s).val=(b j t).val := hs.trans ht.symm
    let av : I → C(Interval,S) := fun k => ⟨fun t => (a k t).val,continuous_subtype_val.comp (a k).continuous⟩
    let bv : J → C(Interval,S) := fun k => ⟨fun t => (b k t).val,continuous_subtype_val.comp (b k).continuous⟩
    have had : ∀ k m,k≠m → Disjoint (range (av k)) (range (av m)) := by
      intro k m hkm
      apply Set.disjoint_left.mpr
      rintro x ⟨r,hr⟩ ⟨t,ht⟩
      have he : a k r=a m t := Subtype.ext (hr.trans ht.symm)
      exact Set.disjoint_left.mp (hadisjoint k m hkm) (mem_range_self r) ⟨t,he.symm⟩
    have hbd : ∀ k m,k≠m → Disjoint (range (bv k)) (range (bv m)) := by
      intro k m hkm
      apply Set.disjoint_left.mpr
      rintro x ⟨r,hr⟩ ⟨t,ht⟩
      have he : b k r=b m t := Subtype.ext (hr.trans ht.symm)
      exact Set.disjoint_left.mp (hbdisjoint k m hkm) (mem_range_self r) ⟨t,he.symm⟩
    have hfin : ((⋃ k,range (av k))∩⋃ k,range (bv k)).Finite := by
      apply (hfinite.image (fun y:↥F => y.val)).subset
      rintro x ⟨hxA,hxB⟩
      obtain ⟨k,r,hr⟩ := mem_iUnion.mp hxA
      obtain ⟨m,t,ht⟩ := mem_iUnion.mp hxB
      refine ⟨a k r,⟨mem_iUnion.mpr ⟨k,mem_range_self r⟩,?_⟩,hr⟩
      exact mem_iUnion.mpr ⟨m,⟨t,Subtype.ext (ht.trans hr.symm)⟩⟩
    obtain ⟨U,hU,hpU,hUF,hUa,hUb,hiso⟩ :=
      ActualHarerWholeGraph.actual_finite_whole_graph_genuine_contact_constructs_isolated_clear_open_neighborhood
        av bv had hbd hfin F i j (q v) ⟨s,hs⟩ ⟨t,ht⟩
        (hs ▸ (a i s).property) hvFront
    have hbemb : ∀ k,IsEmbedding (bv k) := by
      intro k
      exact IsEmbedding.subtypeVal.comp (hb k)
    obtain ⟨Q,hpQ,hQU,hQp,hOther,haxis,htrace⟩ :=
      ActualHarerWholeAnchorRail.actual_disjoint_whole_moving_family_constructs_local_exact_axis_chart
        bv hbemb hbd j t htInterior U hU (by have ht' : (b j t).val=q v := ht; change (b j t).val∈U; rw [ht']; exact hpU)
    have hgInternalClear : ∀ w∈Ioo (0:Interval) 1,g w∉frontier F := by
      intro w hw hFront
      obtain ⟨z,hz⟩ := hgb (mem_range_self w)
      have hzEnd : z=0 ∨ z=1 := by
        by_cases hz0 : z=0
        · exact Or.inl hz0
        by_cases hz1 : z=1
        · exact Or.inr hz1
        have hzInt : z∈Ioo (0:Interval) 1 :=
          ⟨lt_of_le_of_ne z.property.1 (Ne.symm hz0),lt_of_le_of_ne z.property.2 hz1⟩
        exact (hbClear j z hzInt (by have hz' : (b j z).val=g w := hz; rw [hz']; exact hFront)).elim
      have hbvalg : range g⊆range (bv j) := hgb
      have he : g w=bv j 0 ∨ g w=bv j 1 := by
        rcases hzEnd with rfl | rfl
        · exact Or.inl hz.symm
        · exact Or.inr hz.symm
      have hwEnd := CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
        (bv j) g (hbemb j) hg hbvalg w he
      rcases hwEnd with rfl | rfl
      · exact (lt_irrefl (0:Interval)) hw.1
      · exact (lt_irrefl (1:Interval)) hw.2
    have hqInternalClear : ∀ w∈Ioo (0:Interval) 1,q w∉frontier F := by
      intro w hw hFront
      obtain ⟨z,hz⟩ := hqa (mem_range_self w)
      have hzEnd : z=0 ∨ z=1 := by
        by_cases hz0 : z=0
        · exact Or.inl hz0
        by_cases hz1 : z=1
        · exact Or.inr hz1
        have hzInt : z∈Ioo (0:Interval) 1 :=
          ⟨lt_of_le_of_ne z.property.1 (Ne.symm hz0),lt_of_le_of_ne z.property.2 hz1⟩
        exact (haClear i z hzInt (by have hz' : (a i z).val=q w := hz; rw [hz']; exact hFront)).elim
      have he : q w=av i 0 ∨ q w=av i 1 := by
        rcases hzEnd with rfl | rfl
        · exact Or.inl hz.symm
        · exact Or.inr hz.symm
      have hwEnd := CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
        (av i) q (IsEmbedding.subtypeVal.comp (ha i)) hq hqa w he
      rcases hwEnd with rfl | rfl
      · exact (lt_irrefl (0:Interval)) hw.1
      · exact (lt_irrefl (1:Interval)) hw.2
    have hdInteriorF : interior (range d)⊆interior F := interior_mono hdF
    have hdBoundary : frontier (range d)=range q∪range g :=
      (embedded_surface_disk_frontier_eq_boundary_image d hd).trans hboundary
    have hdClear : Disjoint (interior (range d)) ((⋃ k,range (av k))∪⋃ k,range (bv k)) := by
      rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd]
      exact hempty
    have hdFrontierCorners : range d∩frontier F⊆{q 0,q 1} := by
      rintro y ⟨hyD,hyF⟩
      have hyNotInterior : y∉interior (range d) := by
        intro hi
        exact ((mem_frontier_iff_notMem_interior (hdF hyD)).mp hyF) (hdInteriorF hi)
      have hdClosed : IsClosed (range d) := (isCompact_range d.continuous).isClosed
      have hyBoundary : y∈range q∪range g := by
        rw [←hdBoundary,hdClosed.frontier_eq]
        exact ⟨hyD,hyNotInterior⟩
      rcases hyBoundary with ⟨w,hw⟩ | ⟨w,hw⟩
      · by_cases hw0 : w=0
        · left;exact hw0 ▸ hw.symm
        by_cases hw1 : w=1
        · right;exact hw1 ▸ hw.symm
        exact (hqInternalClear w
          ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
          (hw ▸ hyF)).elim
      · by_cases hw0 : w=0
        · left;exact (hw0 ▸ hw.symm).trans hzero.symm
        by_cases hw1 : w=1
        · right;exact (hw1 ▸ hw.symm).trans hone.symm
        exact (hgInternalClear w
          ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
          (hw ▸ hyF)).elim
    have hdAtMostOneFrontier : ∀ x∈range d∩frontier F,∀ y∈range d∩frontier F,x=y := by
      intro x hx y hy
      have hxEnds := hdFrontierCorners hx
      have hyEnds := hdFrontierCorners hy
      rcases hgenuine with h0 | h1
      · have hx1 : x=q 1 := by
          rcases hxEnds with he | he
          · exact (h0 (he ▸ hx.2)).elim
          · exact Set.mem_singleton_iff.mp he
        have hy1 : y=q 1 := by
          rcases hyEnds with he | he
          · exact (h0 (he ▸ hy.2)).elim
          · exact Set.mem_singleton_iff.mp he
        exact hx1.trans hy1.symm
      · have hx0 : x=q 0 := by
          rcases hxEnds with he | he
          · exact he
          · exact (h1 ((Set.mem_singleton_iff.mp he) ▸ hx.2)).elim
        have hy0 : y=q 0 := by
          rcases hyEnds with he | he
          · exact he
          · exact (h1 ((Set.mem_singleton_iff.mp he) ▸ hy.2)).elim
        exact hx0.trans hy0.symm
    have hdOrdinary : q 0∉frontier F → q 1∉frontier F → range d⊆interior F := by
      intro h0 h1 y hyD
      by_contra hn
      have hyFront : y∈frontier F := (mem_frontier_iff_notMem_interior (hdF hyD)).mpr hn
      rcases hdFrontierCorners ⟨hyD,hyFront⟩ with he | he
      · exact h0 (he ▸ hyFront)
      · exact h1 ((Set.mem_singleton_iff.mp he) ▸ hyFront)
    have hgOrdinary : g 0∉frontier F → g 1∉frontier F → range g⊆interior F := by
      intro h0 h1 x hx
      obtain ⟨w,rfl⟩ := hx
      have hgF : g w∈F := by
        obtain ⟨z,hz⟩ := hgb (mem_range_self w)
        exact hz ▸ (b j z).property
      have hgNot : g w∉frontier F := by
        by_cases hw0 : w=0
        · simpa only [hw0] using h0
        by_cases hw1 : w=1
        · simpa only [hw1] using h1
        exact hgInternalClear w
          ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
      by_contra hn
      exact hgNot ((mem_frontier_iff_notMem_interior hgF).mpr hn)
    have hOrdinaryStrip : g 0∉frontier F → g 1∉frontier F →
        ∃ R : Interval×Icc (-1:ℝ) 1→S,IsEmbedding R ∧
          (∀ w,R (w,⟨0,by norm_num⟩)=g w) ∧ range R⊆interior F ∧
          ∀ k,k≠j → Disjoint (range R) (range (bv k)) := by
      intro h0 h1
      let Other : Set S := ⋃ k : {k:J // k≠j},range (bv k.val)
      have hOtherClosed : IsClosed Other := isClosed_iUnion_of_finite
        (fun k : {k:J // k≠j} => (isCompact_range (bv k.val).continuous).isClosed)
      let O : Set S := interior F∩Otherᶜ
      have hO : IsOpen O := isOpen_interior.inter hOtherClosed.isOpen_compl
      have hgO : range g⊆O := by
        intro x hx
        refine ⟨hgOrdinary h0 h1 hx,?_⟩
        intro hxO
        obtain ⟨k,hk⟩ := mem_iUnion.mp hxO
        exact Set.disjoint_left.mp (hbd j k.val (Ne.symm k.property)) (hgb hx) hk
      obtain ⟨R,hR,hcenter,hRO⟩ := source_whole_embedded_arc_strip g hg O hO hgO
      refine ⟨R,hR,hcenter,fun x hx => (hRO hx).1,?_⟩
      intro k hk
      apply Set.disjoint_left.mpr
      intro x hxR hxk
      exact (hRO hxR).2 (mem_iUnion.mpr ⟨⟨k,hk⟩,hxk⟩)
    have haemb : IsEmbedding (av i) := IsEmbedding.subtypeVal.comp (ha i)
    have hpQa : av i s∈Q.source := by
      change (a i s).val∈Q.source
      rw [hcontact]
      exact hpQ
    have hpair : Q.source∩(range (av i)∩range (bv j))={av i s} := by
      ext x
      constructor
      · rintro ⟨hxQ,hxA,hxB⟩
        have hxU : x∈U∩((⋃ k,range (av k))∩⋃ k,range (bv k)) :=
          ⟨hQU hxQ,mem_iUnion.mpr ⟨i,hxA⟩,mem_iUnion.mpr ⟨j,hxB⟩⟩
        rw [hiso] at hxU
        change x=av i s
        exact hxU.trans hs.symm
      · intro hx
        have he : x=av i s := hx
        subst x
        exact ⟨hpQa,mem_range_self s,⟨t,hcontact.symm⟩⟩
    obtain ⟨l,r,hls,hsr,hwin,hleft,hright⟩ :=
      ActualHarerContactSides.actual_isolated_whole_trace_contact_constructs_two_signed_branch_windows
        (av i) (bv j) haemb Q haxis s hsInterior hpQa hpair
    have hQF : Q.source⊆interior F := hQU.trans hUF
    have hFaxis : ∀ y:↥F,y.val∈Q.source → (y∈range (b j) ↔ Q y.val 1=0) := by
      intro y hy
      have hrange : y∈range (b j) ↔ y.val∈range (bv j) := by
        constructor
        · rintro ⟨w,rfl⟩;exact mem_range_self w
        · rintro ⟨w,hw⟩;exact ⟨w,Subtype.ext hw⟩
      exact hrange.trans (haxis y.val hy)
    have hFotherA : ∀ k,k≠i → ∀ y∈range (a k),y.val∉Q.source := by
      intro k hk y hy hyQ
      obtain ⟨w,rfl⟩ := hy
      exact Set.disjoint_left.mp (hUa k hk) (hQU hyQ) (mem_range_self w)
    have hFotherB : ∀ k,k≠j → ∀ y∈range (b k),y.val∉Q.source := by
      intro k hk y hy hyQ
      obtain ⟨w,rfl⟩ := hy
      exact Set.disjoint_left.mp (hOther k hk) hyQ (mem_range_self w)
    have haxisP : Q (av i s) 1=0 := (haxis (av i s) hpQa).mp ⟨t,hcontact.symm⟩
    have hpQv:q v∈Q.source := by
      have he:(b j t).val=q v := ht
      have hp':(b j t).val∈Q.source := hpQ
      exact he ▸ hp'
    rcases hleft with hln|hlp
    · rcases hright with hrn|hrp
      · apply (hTangencyFalse i j s l r Q 1 (Or.inr rfl) hls hsr hpQa haxisP hQF hFaxis hFotherA hFotherB ?_).elim
        intro w hw hws
        rcases lt_or_gt_of_ne hws with hlt|hgt
        · simpa [av] using hln w ⟨hw.1.le,hlt⟩
        · simpa [av] using hrn w ⟨hgt,hw.2.le⟩
      · exact ⟨s,t,l,r,Q,1,hsInterior,htInterior,hs,ht,hls,hsr,Or.inr rfl,hpQv,hQF,hFaxis,hwin,
          by simpa [av] using hln,by simpa [av] using hrp⟩
    · rcases hright with hrn|hrp
      · refine ⟨s,t,l,r,Q,-1,hsInterior,htInterior,hs,ht,hls,hsr,Or.inl rfl,hpQv,hQF,hFaxis,hwin,?_,?_⟩
        · intro w hw;have hh := hlp w hw; change 0<Q (a i w).val 1 at hh;linarith
        · intro w hw;have hh := hrn w hw; change Q (a i w).val 1<0 at hh;linarith
      · apply (hTangencyFalse i j s l r Q (-1) (Or.inl rfl) hls hsr hpQa haxisP hQF hFaxis hFotherA hFotherB ?_).elim
        intro w hw hws
        rcases lt_or_gt_of_ne hws with hlt|hgt
        · have hh := hlp w ⟨hw.1.le,hlt⟩; change 0<Q (a i w).val 1 at hh;linarith
        · have hh := hrp w ⟨hgt,hw.2.le⟩; change 0<Q (a i w).val 1 at hh;linarith
  have hSidesD : range q∪range g⊆range d := by
    rw [←hboundary]
    exact image_subset_range _ _
  have hBoundaryContact : ∀ x∈range d,
      x∈((⋃ k,range (fun t:Interval=>(a k t).val))∪⋃ k,range (fun t:Interval=>(b k t).val)) →
      x∈range q∪range g := by
    intro x hxD hxFamily
    have hn:x∉interior (range d) := by
      intro hxInt
      rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq d hd] at hxInt
      exact Set.disjoint_left.mp hempty hxInt hxFamily
    have hclosed:IsClosed (range d) := (isCompact_range d.continuous).isClosed
    have hxFront:x∈frontier (range d) := by rw [hclosed.frontier_eq];exact ⟨hxD,hn⟩
    rw [embedded_surface_disk_frontier_eq_boundary_image d hd,hboundary] at hxFront
    exact hxFront
  have hcleanA : range d∩(⋃ k,range (fun t:Interval=>(a k t).val))=range q := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxD,hxA⟩
      rcases hBoundaryContact x hxD (Or.inl hxA) with hxQ|hxG
      · exact hxQ
      · have hxB:x∈⋃ k,range (fun t:Interval=>(b k t).val) :=mem_iUnion.mpr ⟨j,hgb hxG⟩
        rcases hNoNoncorner x hxD hxA hxB with hx0|hx1
        · exact ⟨0,hx0.symm⟩
        · exact ⟨1,(mem_singleton_iff.mp hx1).symm⟩
    · intro x hxQ
      exact ⟨hSidesD (Or.inl hxQ),mem_iUnion.mpr ⟨i,hqa hxQ⟩⟩
  have hcleanB : range d∩(⋃ k,range (fun t:Interval=>(b k t).val))=range g := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxD,hxB⟩
      rcases hBoundaryContact x hxD (Or.inr hxB) with hxQ|hxG
      · have hxA:x∈⋃ k,range (fun t:Interval=>(a k t).val) :=mem_iUnion.mpr ⟨i,hqa hxQ⟩
        rcases hNoNoncorner x hxD hxA hxB with hx0|hx1
        · exact ⟨0,hzero.symm.trans hx0.symm⟩
        · exact ⟨1,hone.symm.trans (mem_singleton_iff.mp hx1).symm⟩
      · exact hxG
    · intro x hxG
      exact ⟨hSidesD (Or.inr hxG),mem_iUnion.mpr ⟨j,hgb hxG⟩⟩
  obtain ⟨α,β,old,new,e,hαβ,hOld,hNew,he,hOld0,hOld1,hOldRange,hgOld,hNew0,hNew1,hMeet,hBoundary,hde,heF,hTrace,hFrontier,hAnchor,hContact⟩ :=
    actual_clean_crossing_disk_constructs_whole_moving_trace_comparison_disk
      S F I J a b ha hb hadisjoint hbdisjoint hfinite ha0 ha1 hb0 hb1 haClear hbClear
      i j q g hq hg hqa hgb hzero hone d hd hboundary hdF hempty hgenuine hcleanA hcleanB hCornerCross
  have hParamMeet : ∀ s t:Interval,old s=new t →
      (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
    intro s t hst
    have hx : old s∈({old 0,old 1}:Set S) :=
      hMeet ▸ ⟨mem_range_self s,⟨t,hst.symm⟩⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨hOld.injective hx,hNew.injective (hst.symm.trans (hx.trans hNew0.symm))⟩
    · have hx' := mem_singleton_iff.mp hx
      exact Or.inr ⟨hOld.injective hx',hNew.injective (hst.symm.trans (hx'.trans hNew1.symm))⟩
  have hSidesE : range old∪range new⊆range e := by
    rw [←hBoundary]
    exact image_subset_range _ _
  obtain ⟨g₀,g₁,hg₀,hg₁,hg01,hg11,hcircle,hmeet,hgLift,hhLift⟩ :=
    RegionalEmbeddedFamily.clean_disk_boundary_pair_planar_lifts e he old new
      hOld hNew hNew0 hNew1 hParamMeet hBoundary
  obtain ⟨ψ,hψcircle,hψball,hψclosed,hψg,hψh,hψ0,hψ1⟩ :=
    RegionalEmbeddedFamily.planar_clean_pair_schoenflies_alignment
      g₀ g₁ hg₀ hg₁ hg01 hg11 hmeet hcircle
  obtain ⟨Q,hEQ,hQt⟩ := actual_embedded_closed_disk_constructs_full_plane_ambient_chart e he
  have hkin (z:Plane.closedSquare 0 1) : ψ.symm z.val∈Metric.closedBall (0:Plane) 1 := by
    have hz : z.val∈ψ '' Metric.closedBall (0:Plane) 1 := hψclosed.symm ▸ z.property
    obtain ⟨w,hw,hew⟩ := hz
    rw [←hew,ψ.symm_apply_apply]
    exact hw
  let kin : Plane.closedSquare 0 1 → Metric.closedBall (0:Plane) 1 :=
    fun z => ⟨ψ.symm z.val,hkin z⟩
  have hkinc : Continuous kin := (ψ.symm.continuous.comp continuous_subtype_val).subtype_mk _
  let sq : Plane.closedSquare 0 1 → Plane := fun z => Q (e (kin z))
  have hsqc : Continuous sq := Q.continuousOn.comp_continuous
    (e.continuous.comp hkinc) (fun z => hEQ (mem_range_self _))
  have hsqi : Function.Injective sq := by
    intro z w hh
    have h₁ := Q.injOn (hEQ (mem_range_self (kin z)))
      (hEQ (mem_range_self (kin w))) hh
    have h₂ := congrArg Subtype.val (he.injective h₁)
    exact Subtype.ext (ψ.symm.injective h₂)
  letI : CompactSpace (Plane.closedSquare 0 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  obtain ⟨H,hH⟩ := exists_ambient_extension_of_embedded_closed_square sq
    (hsqc.isClosedEmbedding hsqi).isEmbedding
  let f : Plane → S := Q.symm ∘ H
  have hf : IsOpenEmbedding f := (Q.symm.isOpenEmbedding hQt).comp H.isOpenEmbedding
  have hfψ (z:Metric.closedBall (0:Plane) 1) : f (ψ z.val)=e z := by
    have hz : ψ z.val∈Plane.closedSquare 0 1 := hψclosed ▸ mem_image_of_mem ψ z.property
    have hk : kin ⟨ψ z.val,hz⟩=z := Subtype.ext (ψ.symm_apply_apply z.val)
    change Q.symm (H (ψ z.val))=e z
    rw [hH ⟨ψ z.val,hz⟩]
    change Q.symm (Q (e (kin ⟨ψ z.val,hz⟩)))=e z
    rw [hk,Q.left_inv (hEQ (mem_range_self z))]
  have hfDisk : f '' Plane.closedSquare 0 1=range e := by
    rw [←hψclosed,image_image]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,(hfψ ⟨z,hz⟩).symm⟩
    · rintro ⟨z,rfl⟩
      exact ⟨z.val,z.property,hfψ z⟩
  have hfOld : f '' (sideTop∪sideLeft)=range old := by
    rw [←hψg,image_image]
    ext x
    constructor
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      obtain ⟨z,hz,hez⟩ := hgLift t
      exact ⟨t,hez.symm.trans ((hfψ z).symm.trans (congrArg (fun w=>f (ψ w)) hz))⟩
    · rintro ⟨t,rfl⟩
      obtain ⟨z,hz,hez⟩ := hgLift t
      exact ⟨g₀ t,mem_range_self t,(congrArg (fun w=>f (ψ w)) hz.symm).trans ((hfψ z).trans hez)⟩
  have hfNew : f '' (sideBottom∪sideRight)=range new := by
    rw [←hψh,image_image]
    ext x
    constructor
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      obtain ⟨z,hz,hez⟩ := hhLift t
      exact ⟨t,hez.symm.trans ((hfψ z).symm.trans (congrArg (fun w=>f (ψ w)) hz))⟩
    · rintro ⟨t,rfl⟩
      obtain ⟨z,hz,hez⟩ := hhLift t
      exact ⟨g₁ t,mem_range_self t,(congrArg (fun w=>f (ψ w)) hz.symm).trans ((hfψ z).trans hez)⟩
  have hf0 : f cornerNE=old 0 := by
    obtain ⟨z,hz,hez⟩ := hgLift 0
    rw [←hψ0,←hz,hfψ]
    exact hez
  have hf1 : f cornerSW=old 1 := by
    obtain ⟨z,hz,hez⟩ := hgLift 1
    rw [←hψ1,←hz,hfψ]
    exact hez
  let bv : J → C(Interval,S) := fun k =>
    ⟨fun t => (b k t).val,continuous_subtype_val.comp (b k).continuous⟩
  have hbv : ∀ k,IsEmbedding (bv k) := fun k => IsEmbedding.subtypeVal.comp (hb k)
  have hbd : ∀ k l,k≠l → Disjoint (range (bv k)) (range (bv l)) := by
    intro k l hkl
    apply disjoint_left.mpr
    rintro x ⟨s,hs⟩ ⟨t,ht⟩
    exact disjoint_left.mp (hbdisjoint k l hkl) (mem_range_self s)
      ⟨t,Subtype.ext (ht.trans hs.symm)⟩
  have hOldB : range old⊆range (bv j) := by
    rw [hOldRange]
    exact image_subset_range _ _
  let Tail : Set S := bv j '' (Iic α∪Ici β)
  let Other : Set S := ⋃ k : {k:J // k≠j},range (bv k.val)
  let Z : Set S := ((interior F)ᶜ∪Tail)∪Other
  have hZ : IsClosed Z :=
    (isOpen_interior.isClosed_compl.union
      (((isClosed_Iic.union isClosed_Ici).isCompact).image (bv j).continuous).isClosed).union
      (isClosed_iUnion_of_finite (fun k : {k:J // k≠j} =>
        (isCompact_range (bv k.val).continuous).isClosed))
  have hZ0 : old 0∈Z := Or.inl (Or.inr ⟨α,Or.inl (by simp),hOld0.symm⟩)
  have hZ1 : old 1∈Z := Or.inl (Or.inr ⟨β,Or.inr (by simp),hOld1.symm⟩)
  have hEZ : range e∩Z=({old 0,old 1}:Set S) := by
    apply Subset.antisymm
    · rintro x ⟨hxE,hxZ⟩
      rcases hxZ with (hxF | ⟨t,ht,htx⟩) | hxOther
      · exact hFrontier ⟨hxE,(mem_frontier_iff_notMem_interior (heF hxE)).mpr hxF⟩
      · have hxOld : x∈range old := hTrace ▸ ⟨hxE,mem_iUnion.mpr ⟨j,⟨t,htx⟩⟩⟩
        obtain ⟨w,hw,hwx⟩ := hOldRange ▸ hxOld
        have hwt : w=t := (hbv j).injective (hwx.trans htx.symm)
        subst w
        rcases ht with ht | ht
        · have htα : t=α := le_antisymm ht hw.1
          exact Or.inl (htx.symm.trans ((congrArg (bv j) htα).trans hOld0.symm))
        · have htβ : t=β := le_antisymm hw.2 ht
          exact Or.inr (htx.symm.trans ((congrArg (bv j) htβ).trans hOld1.symm))
      · obtain ⟨k,hk⟩ := mem_iUnion.mp hxOther
        have hxOld : x∈range old := hTrace ▸ ⟨hxE,mem_iUnion.mpr ⟨k.val,hk⟩⟩
        exact (disjoint_left.mp (hbd j k.val k.property.symm) (hOldB hxOld) hk).elim
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨hSidesE (Or.inl (mem_range_self 0)),hZ0⟩
      · have hx' : x=old 1 := mem_singleton_iff.mp hx
        subst x
        exact ⟨hSidesE (Or.inl (mem_range_self 1)),hZ1⟩
  have hMovingBad : ∀ x,x∈⋃ k,range (bv k) → x∉range old → x∈Z := by
    intro x hx hn
    obtain ⟨k,t,ht⟩ := mem_iUnion.mp hx
    by_cases hkj : k=j
    · subst k
      have htNot : t∉Icc α β := fun htIn => hn (hOldRange.symm ▸ ⟨t,htIn,ht⟩)
      have htTail : t∈Iic α∪Ici β := by
        by_cases hαt : α≤t
        · exact Or.inr (le_of_not_ge (fun htβ => htNot ⟨hαt,htβ⟩))
        · exact Or.inl (le_of_not_ge hαt)
      exact Or.inl (Or.inr ⟨t,htTail,ht⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k,hkj⟩,⟨t,ht⟩⟩)
  let fb : Plane → S := f ∘ ψ
  have hfb : IsOpenEmbedding fb := hf.comp ψ.isOpenEmbedding
  have hfbe (z:Metric.closedBall (0:Plane) 1) : fb z.val=e z := hfψ z
  have hfbDisk : fb '' Metric.closedBall (0:Plane) 1=range e := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩;exact ⟨⟨z,hz⟩,(hfbe ⟨z,hz⟩).symm⟩
    · rintro ⟨z,rfl⟩;exact ⟨z.val,z.property,hfbe z⟩
  have hfbOld (t:Interval) : fb (g₀ t)=old t := by
    obtain ⟨z,hz,hez⟩ := hgLift t
    rw [←hz,hfbe]
    exact hez
  have hfbNew (t:Interval) : fb (g₁ t)=new t := by
    obtain ⟨z,hz,hez⟩ := hhLift t
    rw [←hz,hfbe]
    exact hez
  have hgSphere (t:Interval) : g₀ t∈Metric.sphere (0:Plane) 1 := by
    rw [←hcircle];exact Or.inl (mem_range_self t)
  have hhSphere (t:Interval) : g₁ t∈Metric.sphere (0:Plane) 1 := by
    rw [←hcircle];exact Or.inr (mem_range_self t)
  let Forbidden : Set Plane := fb ⁻¹' Z
  have hForbidden : IsClosed Forbidden := hZ.preimage hfb.continuous
  have hForbidden0 : g₀ 0∈Forbidden := by change fb (g₀ 0)∈Z;rw [hfbOld];exact hZ0
  have hForbidden1 : g₀ 1∈Forbidden := by change fb (g₀ 1)∈Z;rw [hfbOld];exact hZ1
  obtain ⟨L,_,hLForbidden,hLInterior,hLFix⟩ :=
    closed_ball_actual_forbidden_avoiding_enlargement Forbidden univ hForbidden
      ⟨g₀ 0,hForbidden0⟩ isOpen_univ (subset_univ _)
  have hL0 : L.symm (g₀ 0)=g₀ 0 :=
    hLFix _ (by simpa only [Metric.mem_sphere,dist_zero_right] using hgSphere 0) hForbidden0
  have hL1 : L.symm (g₀ 1)=g₀ 1 :=
    hLFix _ (by simpa only [Metric.mem_sphere,dist_zero_right] using hgSphere 1) hForbidden1
  let θ : Plane ≃ₜ Plane := L.symm.trans ψ
  have hθ0 : θ (g₀ 0)=cornerNE := by change ψ (L.symm (g₀ 0))=cornerNE;rw [hL0,hψ0]
  have hθ1 : θ (g₀ 1)=cornerSW := by change ψ (L.symm (g₀ 1))=cornerSW;rw [hL1,hψ1]
  let pa : C(Interval,Plane) := ⟨θ ∘ g₀,θ.continuous.comp g₀.continuous⟩
  let pb : C(Interval,Plane) := ⟨θ ∘ g₁,θ.continuous.comp g₁.continuous⟩
  have hpa : IsEmbedding pa := θ.isEmbedding.comp hg₀
  have hpb : IsEmbedding pb := θ.isEmbedding.comp hg₁
  let M : Plane → S := fb ∘ L ∘ ψ.symm
  have hM : IsOpenEmbedding M := (hfb.comp L.isOpenEmbedding).comp ψ.symm.isOpenEmbedding
  have hMθ (z:Plane) : M (θ z)=fb z := by
    change fb (L (ψ.symm (ψ (L.symm z))))=fb z
    rw [ψ.symm_apply_apply,L.apply_symm_apply]
  have hMpa (t:Interval) : M (pa t)=old t := (hMθ _).trans (hfbOld t)
  have hMpb (t:Interval) : M (pb t)=new t := (hMθ _).trans (hfbNew t)
  let E : OpenPartialHomeomorph S Plane := (hM.toOpenPartialHomeomorph M).symm
  have hEs : E.source=range M := hM.toOpenPartialHomeomorph_target M
  have hEt : E.target=univ := hM.toOpenPartialHomeomorph_source M
  have hEM (z:Plane) : E (M z)=z := hM.toOpenPartialHomeomorph_left_inv M
  have hME (x:S) (hx:x∈E.source) : M (E x)=x :=
    hM.toOpenPartialHomeomorph_right_inv M (hEs ▸ hx)
  have hPull (K:Set Plane) : {x:S | x∈E.source ∧ E x∈K}=M '' K := by
    ext x
    constructor
    · intro hx;exact ⟨E x,hx.2,hME x hx.1⟩
    · rintro ⟨z,hz,rfl⟩;exact ⟨hEs.symm ▸ mem_range_self z,by rw [hEM];exact hz⟩
  have hPullOld : {x:S | x∈E.source ∧ E x∈range pa}=range old := by
    rw [hPull,←range_comp]
    exact congrArg range (funext hMpa)
  have hPullNew : {x:S | x∈E.source ∧ E x∈range pb}=range new := by
    rw [hPull,←range_comp]
    exact congrArg range (funext hMpb)
  have hpa0 : pa 0=cornerNE := hθ0
  have hpa1 : pa 1=cornerSW := hθ1
  have hpb0 : pb 0=cornerNE := by change θ (g₁ 0)=cornerNE;rw [←hg01,hθ0]
  have hpb1 : pb 1=cornerSW := by change θ (g₁ 1)=cornerSW;rw [←hg11,hθ1]
  have hAvoidInterior (z:Plane) (hz:z∈Metric.closedBall (0:Plane) 1) (hn:fb z∉Z) :
      θ z∈Plane.openSquare 0 1 := by
    have hzi : z∈L '' Metric.ball (0:Plane) 1 := hLInterior ⟨hz,hn⟩
    obtain ⟨w,hw,hew⟩ := hzi
    change ψ (L.symm z)∈Plane.openSquare 0 1
    rw [←hew,L.symm_apply_apply]
    exact hψball ▸ mem_image_of_mem ψ hw
  have hOldAway (t:Interval) (ht:old t∉({old 0,old 1}:Set S)) : old t∉Z := by
    intro htZ
    exact ht (hEZ ▸ ⟨hSidesE (Or.inl (mem_range_self t)),htZ⟩)
  have hNewAway (t:Interval) (ht:new t∉({old 0,old 1}:Set S)) : new t∉Z := by
    intro htZ
    exact ht (hEZ ▸ ⟨hSidesE (Or.inr (mem_range_self t)),htZ⟩)
  have hpaInterior : range pa\{cornerNE,cornerSW}⊆Plane.openSquare 0 1 := by
    rintro z ⟨⟨t,rfl⟩,hn⟩
    have ht:old t∉({old 0,old 1}:Set S) := by
      intro ht
      rcases ht with ht|ht
      · have htt := hOld.injective ht
        exact hn (Or.inl (htt ▸ hpa0))
      · have ht' := mem_singleton_iff.mp ht
        have htt := hOld.injective ht'
        exact hn (Or.inr (mem_singleton_iff.mpr (htt ▸ hpa1)))
    exact hAvoidInterior _ (Metric.sphere_subset_closedBall (hgSphere t)) (by rw [hfbOld];exact hOldAway t ht)
  have hpbInterior : range pb\{cornerNE,cornerSW}⊆Plane.openSquare 0 1 := by
    rintro z ⟨⟨t,rfl⟩,hn⟩
    have ht:new t∉({old 0,old 1}:Set S) := by
      intro ht
      rcases ht with ht|ht
      · have htt := hNew.injective (ht.trans hNew0.symm)
        exact hn (Or.inl (htt ▸ hpb0))
      · have htt := hNew.injective ((mem_singleton_iff.mp ht).trans hNew1.symm)
        exact hn (Or.inr (mem_singleton_iff.mpr (htt ▸ hpb1)))
    exact hAvoidInterior _ (Metric.sphere_subset_closedBall (hhSphere t)) (by rw [hfbNew];exact hNewAway t ht)
  have hSWcurve : cornerSW∈modelCurve := by norm_num [modelCurve,cornerSW,Plane.mk,Plane.supNorm]
  have hpaClosed : range pa⊆Plane.closedSquare 0 1 :=
    crosscut_subset_closedSquare cornerNE_mem_modelCurve hSWcurve hpaInterior
  have hpbClosed : range pb⊆Plane.closedSquare 0 1 :=
    crosscut_subset_closedSquare cornerNE_mem_modelCurve hSWcurve hpbInterior
  have hM0 : M cornerNE=old 0 := by rw [←hpa0,hMpa]
  have hM1 : M cornerSW=old 1 := by rw [←hpa1,hMpa]
  have hSupportZ : (M '' Plane.closedSquare 0 1)∩Z⊆({old 0,old 1}:Set S) := by
    rintro x ⟨⟨z,hz,rfl⟩,hxZ⟩
    let w : Plane := L (ψ.symm z)
    have hwExpanded : w∈L '' Metric.closedBall (0:Plane) 1 :=
      ⟨ψ.symm z,hkin ⟨z,hz⟩,rfl⟩
    have hwForbidden : w∈Forbidden := hxZ
    have hwBoth : w∈Metric.closedBall (0:Plane) 1∩Forbidden := by
      rw [←hLForbidden];exact ⟨hwExpanded,hwForbidden⟩
    have hwDisk := hwBoth.1
    apply hEZ ▸ (show M z∈range e∩Z from ⟨?_,hxZ⟩)
    change fb w∈range e
    rw [←hfbDisk]
    exact mem_image_of_mem fb hwDisk
  have hNEout : cornerNE∉Plane.openSquare 0 1 := by
    have h := cornerNE_mem_modelCurve
    rw [modelCurve_eq_frontier] at h
    intro hz
    exact h.2 (by rwa [Plane.interior_closedSquare])
  have hSWout : cornerSW∉Plane.openSquare 0 1 := by
    have h := hSWcurve
    rw [modelCurve_eq_frontier] at h
    intro hz
    exact h.2 (by rwa [Plane.interior_closedSquare])
  have hOpenNotZ : ∀ x∈M '' Plane.openSquare 0 1,x∉Z := by
    rintro x ⟨z,hz,rfl⟩ hxZ
    have hzClosed : z∈Plane.closedSquare 0 1 :=
      mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hz).le
    rcases hSupportZ ⟨mem_image_of_mem M hzClosed,hxZ⟩ with he|he
    · have hz0 : z=cornerNE := hM.isEmbedding.injective (he.trans hM0.symm)
      exact hNEout (hz0 ▸ hz)
    · have hz1 : z=cornerSW := hM.isEmbedding.injective ((mem_singleton_iff.mp he).trans hM1.symm)
      exact hSWout (hz1 ▸ hz)
  have hOpenF : M '' Plane.openSquare 0 1⊆interior F := by
    intro x hx
    by_contra hn
    exact hOpenNotZ x hx (Or.inl (Or.inl hn))
  have hOldSupport : range old⊆M '' Plane.closedSquare 0 1 := by
    rintro x ⟨t,rfl⟩
    exact ⟨pa t,hpaClosed (mem_range_self t),hMpa t⟩
  have hSupportMoving : (M '' Plane.closedSquare 0 1)∩(⋃ k,range (bv k))=range old := by
    apply Subset.antisymm
    · rintro x ⟨hx,hxB⟩
      by_contra hn
      have hxZ := hMovingBad x hxB hn
      rcases hSupportZ ⟨hx,hxZ⟩ with he|he
      · exact hn ⟨0,he.symm⟩
      · exact hn ⟨1,(mem_singleton_iff.mp he).symm⟩
    · intro x hx
      exact ⟨hOldSupport hx,mem_iUnion.mpr ⟨j,hOldB hx⟩⟩
  have hBmem (k:J) (y:↥F) : y∈range (b k) ↔ y.val∈range (bv k) := by
    constructor
    · rintro ⟨t,rfl⟩;exact mem_range_self t
    · rintro ⟨t,ht⟩;exact ⟨t,Subtype.ext ht⟩
  have hBAllmem (y:↥F) : y∈⋃ k,range (b k) ↔ y.val∈⋃ k,range (bv k) := by
    simp only [mem_iUnion]
    exact exists_congr (fun k=>hBmem k y)
  have hAAllmem (y:↥F) : y∈⋃ k,range (a k) ↔
      y.val∈⋃ k,range (fun t:Interval=>(a k t).val) := by
    constructor
    · intro hy
      obtain ⟨k,hk⟩ := mem_iUnion.mp hy
      obtain ⟨t,rfl⟩ := hk
      exact mem_iUnion.mpr ⟨k,mem_range_self t⟩
    · intro hy
      obtain ⟨k,t,ht⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨k,⟨t,Subtype.ext ht⟩⟩
  have hSelectedTrace :
      ({y:↥F | y.val∈{z:S | z∈E.source ∧ E z∈Plane.closedSquare 0 1}}∩range (b j))=
        {y:↥F | y.val∈{z:S | z∈E.source ∧ E z∈range pa}} := by
    rw [hPullOld,hPull]
    ext y
    constructor
    · rintro ⟨hyS,hyB⟩
      exact hSupportMoving ▸ ⟨hyS,mem_iUnion.mpr ⟨j,(hBmem j y).mp hyB⟩⟩
    · intro hyOld
      exact ⟨hOldSupport hyOld,(hBmem j y).mpr (hOldB hyOld)⟩
  have hNewRetains :
      ({y:↥F | y.val∈{z:S | z∈E.source ∧ E z∈range pb}}∩(⋃ k,range (a k)))⊆
        (⋃ k,range (b k))∩(⋃ k,range (a k)) := by
    rw [hPullNew]
    rintro y ⟨hyNew,hyA⟩
    have hyEnds : y.val∈({old 0,old 1}:Set S) := by
      by_contra hn
      exact disjoint_left.mp hAnchor ⟨hyNew,hn⟩ ((hAAllmem y).mp hyA)
    have hyOld : y.val∈range old := by
      rcases hyEnds with he|he
      · exact ⟨0,he.symm⟩
      · exact ⟨1,(mem_singleton_iff.mp he).symm⟩
    exact ⟨(hBAllmem y).mpr (mem_iUnion.mpr ⟨j,hOldB hyOld⟩),hyA⟩
  have hDrops : ∃ p:↥F,
      p∈{y:↥F | y.val∈{z:S | z∈E.source ∧ E z∈range pa}}∩(⋃ k,range (a k)) ∧
      p∉{y:↥F | y.val∈{z:S | z∈E.source ∧ E z∈range pb}} := by
    obtain ⟨v,hv,hvFront,hvOld,hvEnds⟩ := hContact
    obtain ⟨t,ht⟩ := hqa (mem_range_self v)
    let p:↥F := ⟨q v,heF (hSidesE (Or.inl hvOld))⟩
    refine ⟨p,?_,?_⟩
    · rw [hPullOld]
      exact ⟨hvOld,mem_iUnion.mpr ⟨i,⟨t,Subtype.ext ht⟩⟩⟩
    · rw [hPullNew]
      intro hvNew
      exact hvEnds (hMeet ▸ ⟨hvOld,hvNew⟩)
  have hOtherMoving : ∀ k,k≠j → ∀ y∈range (b k),
      y.val∉{z:S | z∈E.source ∧ E z∈Plane.openSquare 0 1} := by
    intro k hk y hy hyOpen
    rw [hPull] at hyOpen
    exact hOpenNotZ y.val hyOpen (Or.inr (mem_iUnion.mpr ⟨⟨k,hk⟩,(hBmem k y).mp hy⟩))
  apply hNot
  refine ⟨j,E,range pa,range pb,cornerNE,cornerSW,?_,?_,?_,cornerNE_mem_modelCurve,
    hSWcurve,hpaInterior,hpbInterior,?_,?_,hSelectedTrace,hNewRetains,hDrops,hOtherMoving⟩
  · rw [hEt];exact subset_univ _
  · simpa only [hpa0,hpa1] using RegionalEmbeddedFamily.planar_embedded_path_isArcBetween pa hpa
  · simpa only [hpb0,hpb1] using RegionalEmbeddedFamily.planar_embedded_path_isArcBetween pb hpb
  · rw [hPull];exact hOpenF
  · rw [hPullOld];exact (fun x hx=>heF (hSidesE (Or.inl hx)))

end ActualHarerSupportedBypass
