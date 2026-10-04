import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.MetricSpace.Thickening
import CurveComplexGenusTwo.Topology.ActualHarerBoundary.ActualDiskBoundaryTwoArcsEndpointOrientation
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalFirstDiskActualCoverAssemblyProved
import ClassificationOfSurfaces.Moise.PlaneCycle
import CurveComplexGenusTwo.Topology.ActualSourceGeometry.ActualOneEndpointRegionalFullWidthBand
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualCurveDensity
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import CurveComplexGenusTwo.Topology.CapBandGeometry.CapSide
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
import ClassificationOfSurfaces.Moise.NoRetraction
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.Basic

set_option maxHeartbeats 4000000

open CurveComplex Set Topology

private theorem actual_negative_halfplane_chart_ray_continuation
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (a : C(Interval,↥F))
    (N : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ)
    (hp : (a 0).val∈N.source) (hzero : N (a 0).val=0)
    (hη : 0<η) (htarget : Schoenflies.Plane.openSquare 0 η⊆N.target)
    (hF : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
      y∈F ↔ 0≤N y 0)
    (v : Schoenflies.Plane) (hv : v∈Schoenflies.Plane.openSquare 0 η)
    (hvneg : v 0<0) :
    ∃ r : C(Interval,S),Topology.IsEmbedding r ∧ r 0=(a 0).val ∧
      (∀ t : Interval,0<t → r t∉F) ∧
      Set.range r ∩ Set.range (fun t => (a t).val)={(a 0).val} ∧
      (∀ t,r t∈N.symm '' Schoenflies.Plane.openSquare 0 η) := by
  have h0 : (0:Schoenflies.Plane)∈Schoenflies.Plane.openSquare 0 η := by
    simp [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,hη]
  let f : C(Interval,Schoenflies.Plane) := ⟨fun t => (t:ℝ) • v,by fun_prop⟩
  have hf : ∀ t,f t∈Schoenflies.Plane.openSquare 0 η := by
    intro t
    have hc := Schoenflies.Plane.convex_openSquare 0 η h0 hv
      (sub_nonneg.mpr t.property.2) t.property.1
      (by ring : (1-(t:ℝ))+(t:ℝ)=1)
    simpa [f] using hc
  let r : C(Interval,S) := ⟨fun t => N.symm (f t),
    N.continuousOn_symm.comp_continuous f.continuous (fun t => htarget (hf t))⟩
  have hr0 : r 0=(a 0).val := by
    change N.symm ((0:ℝ) • v)=(a 0).val
    rw [zero_smul,←hzero,N.left_inv hp]
  have hvne : v≠0 := by
    intro he
    have : v 0=0 := by rw [he];rfl
    linarith
  have hri : Function.Injective r := by
    intro t s he
    have hfs := N.symm.injOn (htarget (hf t)) (htarget (hf s)) he
    have hval := (smul_left_injective ℝ hvne) hfs
    exact Subtype.ext hval
  have hrpatch : ∀ t,r t∈N.symm '' Schoenflies.Plane.openSquare 0 η :=
    fun t => ⟨f t,hf t,rfl⟩
  have hrout : ∀ t : Interval,0<t → r t∉F := by
    intro t ht hin
    have hcoord := (hF (r t) (hrpatch t)).mp hin
    change 0≤N (N.symm (f t)) 0 at hcoord
    rw [N.right_inv (htarget (hf t))] at hcoord
    change 0≤(t:ℝ)*v 0 at hcoord
    exact (not_le_of_gt (mul_neg_of_pos_of_neg (show 0<(t:ℝ) from ht) hvneg)) hcoord
  refine ⟨r,(r.continuous.isClosedEmbedding hri).isEmbedding,hr0,hrout,?_,hrpatch⟩
  ext y
  constructor
  · rintro ⟨⟨t,ht⟩,⟨s,hs⟩⟩
    have ht0 : t=0 := by
      by_contra hn
      exact hrout t (bot_lt_iff_ne_bot.mpr hn) (ht ▸ hs ▸ (a s).property)
    simpa only [ht0,hr0,Set.mem_singleton_iff] using ht.symm
  · intro hy
    have he : y=(a 0).val := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨⟨0,hr0⟩,⟨0,rfl⟩⟩

private theorem actual_negative_chart_halfplane_ray_from_positive_square
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (a : C(Interval,↥F))
    (N : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ)
    (hp : (a 0).val∈N.source) (hzero : N (a 0).val=0)
    (hη : 0<η) (htarget : Schoenflies.Plane.openSquare 0 η⊆N.target)
    (hF : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
      y∈F ↔ 0≤N y 0) :
    ∃ r : C(Interval,S),Topology.IsEmbedding r ∧ r 0=(a 0).val ∧
      (∀ t : Interval,0<t → r t∉F) ∧
      Set.range r ∩ Set.range (fun t => (a t).val)={(a 0).val} ∧
      (∀ t,r t∈N.symm '' Schoenflies.Plane.openSquare 0 η) := by
  let v : Schoenflies.Plane := Schoenflies.Plane.mk (-η/2) 0
  have hvneg : v 0<0 := by dsimp [v];linarith
  have hv : v∈Schoenflies.Plane.openSquare 0 η := by
    change max |(-η/2)-0| |(0:ℝ)-0|<η
    rw [sub_zero,sub_zero,abs_of_neg (show -η/2<0 by linarith),abs_zero,max_eq_left (by linarith)]
    linarith
  exact actual_negative_halfplane_chart_ray_continuation F a N η hp hzero hη htarget hF v hv hvneg

private theorem actual_negative_terminal_chart_ray_beyond_essential_circle
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F C : Set S) (a : C(Interval,↥F))
    (N : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ)
    (hp : (a 1).val∈N.source) (hzero : N (a 1).val=0)
    (hη : 0<η) (htarget : Schoenflies.Plane.openSquare 0 η⊆N.target)
    (hlocal : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
      y∈interior F ∧
      (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
      (y∈C ↔ N y 0=0)) :
    ∃ r : C(Interval,S),Topology.IsEmbedding r ∧ r 0=(a 1).val ∧
      (∀ t,r t∈interior F) ∧
      (∀ t : Interval,0<t → r t∉C) ∧
      Set.range r ∩ Set.range (fun t => (a t).val)={(a 1).val} ∧
      (∀ t,r t∈N.symm '' Schoenflies.Plane.openSquare 0 η) := by
  let v : Schoenflies.Plane := Schoenflies.Plane.mk (-η/2) 0
  have hvneg : v 0<0 := by dsimp [v];linarith
  have hvne : v≠0 := by
    intro he
    have : v 0=0 := by rw [he];rfl
    linarith
  have hv : v∈Schoenflies.Plane.openSquare 0 η := by
    change max |(-η/2)-0| |(0:ℝ)-0|<η
    rw [sub_zero,sub_zero,abs_of_neg (show -η/2<0 by linarith),abs_zero,max_eq_left (by linarith)]
    linarith
  have h0 : (0:Schoenflies.Plane)∈Schoenflies.Plane.openSquare 0 η := by
    simp [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,hη]
  let f : C(Interval,Schoenflies.Plane) := ⟨fun t => (t:ℝ) • v,by fun_prop⟩
  have hf : ∀ t,f t∈Schoenflies.Plane.openSquare 0 η := by
    intro t
    have hc := Schoenflies.Plane.convex_openSquare 0 η h0 hv
      (sub_nonneg.mpr t.property.2) t.property.1
      (by ring : (1-(t:ℝ))+(t:ℝ)=1)
    simpa [f] using hc
  let r : C(Interval,S) := ⟨fun t => N.symm (f t),
    N.continuousOn_symm.comp_continuous f.continuous (fun t => htarget (hf t))⟩
  have hr0 : r 0=(a 1).val := by
    change N.symm ((0:ℝ) • v)=(a 1).val
    rw [zero_smul,←hzero,N.left_inv hp]
  have hri : Function.Injective r := by
    intro t s he
    have hfs := N.symm.injOn (htarget (hf t)) (htarget (hf s)) he
    exact Subtype.ext ((smul_left_injective ℝ hvne) hfs)
  have hrpatch : ∀ t,r t∈N.symm '' Schoenflies.Plane.openSquare 0 η :=
    fun t => ⟨f t,hf t,rfl⟩
  have hrcoord : ∀ t,N (r t) 0=(t:ℝ)*v 0 := by
    intro t
    change N (N.symm (f t)) 0=(t:ℝ)*v 0
    rw [N.right_inv (htarget (hf t))]
    rfl
  have hrneg : ∀ t : Interval,0<t → N (r t) 0<0 := by
    intro t ht
    rw [hrcoord]
    exact mul_neg_of_pos_of_neg (show 0<(t:ℝ) from ht) hvneg
  have hrC : ∀ t : Interval,0<t → r t∉C := by
    intro t ht hin
    have he := (hlocal (r t) (hrpatch t)).2.2.mp hin
    exact (ne_of_lt (hrneg t ht)) he
  refine ⟨r,(r.continuous.isClosedEmbedding hri).isEmbedding,hr0,
    fun t => (hlocal _ (hrpatch t)).1,hrC,?_,hrpatch⟩
  ext y
  constructor
  · rintro ⟨⟨t,ht⟩,ha⟩
    have ht0 : t=0 := by
      by_contra hn
      have hpos := ((hlocal _ (hrpatch t)).2.1.mp (ht.symm ▸ ha)).1
      exact (not_le_of_gt (hrneg t (bot_lt_iff_ne_bot.mpr hn))) hpos
    simpa only [ht0,hr0,Set.mem_singleton_iff] using ht.symm
  · intro hy
    have he : y=(a 1).val := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨⟨0,hr0⟩,⟨1,rfl⟩⟩

private theorem actual_simple_path_concat {X : Type} [TopologicalSpace X]
      {x y z : X} (γ : Path x y) (δ : Path y z)
      (hγ : Function.Injective γ) (hδ : Function.Injective δ)
      (hinter : Set.range γ ∩ Set.range δ = {y}) :
      Function.Injective (γ.trans δ) := by
    intro s t hst
    rw [Path.trans_apply, Path.trans_apply] at hst
    by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2 <;>
      simp only [dite_eq_left, hs, ht] at hst
    · have heq := hγ hst
      apply Subtype.ext
      have hval := congrArg Subtype.val heq
      dsimp at hval
      linarith
    · let a : unitInterval := ⟨2 * s,
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩
      let b : unitInterval := ⟨2 * t - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have hmem : γ a ∈ Set.range γ ∩ Set.range δ :=
        ⟨⟨a, rfl⟩, ⟨b, hst.symm⟩⟩
      have hjoin : γ a = y := by
        have : γ a ∈ ({y} : Set X) := hinter ▸ hmem
        simpa using this
      have ha : a = (1 : unitInterval) := hγ (hjoin.trans γ.target.symm)
      have hb : b = (0 : unitInterval) := hδ (hst.symm.trans (hjoin.trans δ.source.symm))
      apply Subtype.ext
      have ha' := congrArg Subtype.val ha
      have hb' := congrArg Subtype.val hb
      dsimp [a, b] at ha' hb'
      linarith
    · let a : unitInterval := ⟨2 * t,
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      let b : unitInterval := ⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩
      have hmem : γ a ∈ Set.range γ ∩ Set.range δ :=
        ⟨⟨a, rfl⟩, ⟨b, hst⟩⟩
      have hjoin : γ a = y := by
        have : γ a ∈ ({y} : Set X) := hinter ▸ hmem
        simpa using this
      have ha : a = (1 : unitInterval) := hγ (hjoin.trans γ.target.symm)
      have hb : b = (0 : unitInterval) := hδ (hst.trans (hjoin.trans δ.source.symm))
      apply Subtype.ext
      have ha' := congrArg Subtype.val ha
      have hb' := congrArg Subtype.val hb
      dsimp [a, b] at ha' hb'
      linarith
    · have heq := hδ hst
      apply Subtype.ext
      have hval := congrArg Subtype.val heq
      dsimp at hval
      linarith

private theorem actual_two_negative_rays_extend_regional_connector
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F G : Set S) (hF : IsClosed F) (hG : G⊆frontier F)
    (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
    (hclear : ∀ t,(a t).val∉G)
    (r₀ r₁ : C(Interval,S))
    (hr₀ : Topology.IsEmbedding r₀) (hr₁ : Topology.IsEmbedding r₁)
    (hzero₀ : r₀ 0=(a 0).val) (hzero₁ : r₁ 0=(a 1).val)
    (hout : ∀ t : Interval,0<t → r₀ t∉F)
    (hin : ∀ t,r₁ t∈interior F)
    (htrace₀ : Set.range r₀∩Set.range (fun t => (a t).val)={(a 0).val})
    (htrace₁ : Set.range r₁∩Set.range (fun t => (a t).val)={(a 1).val})
    (hd : Disjoint (Set.range r₀) (Set.range r₁)) :
    ∃ r : C(Interval,S),Topology.IsEmbedding r ∧
      r 0=r₀ 1 ∧ r 1=r₁ 1 ∧ r 0∉F ∧ (∀ t,r t∉G) ∧
      Set.range r=(Set.range r₀ ∪ Set.range (fun t => (a t).val))∪Set.range r₁ := by
  let p₀ : Path (a 0).val (r₀ 1) :=
    { toContinuousMap := r₀
      source' := hzero₀
      target' := rfl }
  let p : Path (a 0).val (a 1).val :=
    { toContinuousMap := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
      source' := rfl
      target' := rfl }
  let p₁ : Path (a 1).val (r₁ 1) :=
    { toContinuousMap := r₁
      source' := hzero₁
      target' := rfl }
  have hp₀ : Function.Injective p₀ := hr₀.injective
  have hp : Function.Injective p :=
    fun s t h => ha.injective (Subtype.ext h)
  have hp₁ : Function.Injective p₁ := hr₁.injective
  have hranges : Set.range p₀.symm=Set.range r₀ := Path.symm_range p₀
  have hfirst : Set.range p₀.symm∩Set.range p={(a 0).val} := by
    rw [hranges]
    exact htrace₀
  have hfirstinj := actual_simple_path_concat p₀.symm p
    (hp₀.comp unitInterval.symm_involutive.injective) hp hfirst
  have hlast : Set.range (p₀.symm.trans p)∩Set.range p₁={(a 1).val} := by
    rw [Path.trans_range,Set.union_inter_distrib_right,hranges]
    have he : Set.range r₀∩Set.range r₁=∅ := Set.disjoint_iff_inter_eq_empty.mp hd
    have hpint : Set.range p∩Set.range p₁={(a 1).val} := by
      rw [Set.inter_comm]
      exact htrace₁
    have he' : Set.range r₀∩Set.range p₁=∅ := he
    rw [he',hpint,Set.empty_union]
  let P := (p₀.symm.trans p).trans p₁
  have hPi := actual_simple_path_concat (p₀.symm.trans p) p₁ hfirstinj hp₁ hlast
  let r : C(Interval,S) := ⟨P.toFun,P.continuous⟩
  have hrrange : Set.range r=(Set.range r₀∪Set.range (fun t => (a t).val))∪Set.range r₁ := by
    change Set.range P=_
    rw [Path.trans_range,Path.trans_range,hranges]
    rfl
  have hrclear : ∀ t,r t∉G := by
    intro t hg
    have hm := hrrange ▸ (Set.mem_range_self t : r t∈Set.range r)
    rcases hm with (⟨u,hu⟩ | ⟨u,hu⟩) | ⟨u,hu⟩
    · rw [←hu] at hg
      by_cases hu0 : u=0
      · exact hclear 0 (by simpa only [hu0,hzero₀] using hg)
      · exact hout u (bot_lt_iff_ne_bot.mpr hu0) (hF.frontier_subset (hG hg))
    · change (a u).val=r t at hu
      rw [←hu] at hg
      exact hclear u hg
    · rw [←hu] at hg
      exact Set.disjoint_left.mp disjoint_interior_frontier (hin u) (hG hg)
  refine ⟨r,(r.continuous.isClosedEmbedding hPi).isEmbedding,
    P.source,P.target,?_,hrclear,hrrange⟩
  exact (P.source.symm ▸ hout 1 (by norm_num))

private theorem actual_extended_regional_connector_retained_clear_whole_strip
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Schoenflies.Plane S]
    (F G : Set S) (hF : IsClosed F) (hGclosed : IsClosed G) (hG : G⊆frontier F)
    (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
    (hclear : ∀ t,(a t).val∉G)
    (r₀ r₁ : C(Interval,S))
    (hr₀ : Topology.IsEmbedding r₀) (hr₁ : Topology.IsEmbedding r₁)
    (hzero₀ : r₀ 0=(a 0).val) (hzero₁ : r₁ 0=(a 1).val)
    (hout : ∀ t : Interval,0<t → r₀ t∉F)
    (hin : ∀ t,r₁ t∈interior F)
    (htrace₀ : Set.range r₀∩Set.range (fun t => (a t).val)={(a 0).val})
    (htrace₁ : Set.range r₁∩Set.range (fun t => (a t).val)={(a 1).val})
    (hd : Disjoint (Set.range r₀) (Set.range r₁)) :
    ∃ (r : C(Interval,S)) (E : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S)),
      Topology.IsEmbedding r ∧ Topology.IsEmbedding E ∧
      r 0=r₀ 1 ∧ r 1=r₁ 1 ∧ r 0∉F ∧
      (∀ t,E (t,⟨0,by norm_num⟩)=r t) ∧
      (∀ z,E z∉G) ∧
      Set.range r=(Set.range r₀∪Set.range (fun t => (a t).val))∪Set.range r₁ := by
  obtain ⟨r,hr,hr0,hr1,hrout,hrclear,hrrange⟩ :=
    actual_two_negative_rays_extend_regional_connector
      F G hF hG a ha hclear r₀ r₁ hr₀ hr₁ hzero₀ hzero₁ hout hin htrace₀ htrace₁ hd
  have hU : IsOpen Gᶜ := hGclosed.isOpen_compl
  have hrU : Set.range r⊆Gᶜ := by
    rintro y ⟨t,rfl⟩
    exact hrclear t
  obtain ⟨E,hE,hcenter,hEU⟩ := source_whole_embedded_arc_strip r hr Gᶜ hU hrU
  let E' : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S) := ⟨E,hE.continuous⟩
  exact ⟨r,E',hr,hE,hr0,hr1,hrout,hcenter,
    fun z => hEU (Set.mem_range_self z),hrrange⟩

private theorem actual_three_piece_connector_exact_affine_tail_clocks
    {X : Type} [TopologicalSpace X]
    {x y z w : X} (p₀ : Path x y) (p : Path y z) (p₁ : Path z w) :
    (∀ t : Interval,1/2≤(t:ℝ) →
      ((p₀.trans p).trans p₁) t=p₁.extend (2*(t:ℝ)-1)) ∧
    (∀ t : Interval,1/4≤(t:ℝ) → (t:ℝ)≤1/2 →
      ((p₀.trans p).trans p₁) t=p.extend (4*(t:ℝ)-1)) := by
  constructor
  · intro t ht
    rw [←Path.extend_apply,Path.extend_trans_of_half_le _ _ ht]
  · intro t htlo hthi
    rw [←Path.extend_apply,Path.extend_trans_of_le_half _ _ hthi,
      Path.extend_trans_of_half_le _ _ (by linarith : 1/2≤2*(t:ℝ))]
    congr 1
    ring

private theorem actual_three_piece_connector_terminal_chart_control
    {X : Type} [TopologicalSpace X]
    {x y z w : X} (p₀ : Path x y) (p : Path y z) (p₁ : Path z w)
    (θ α : Interval) (hθlo : 1/4≤(θ:ℝ)) (hθhi : (θ:ℝ)≤1/2)
    (hα : (α:ℝ)=4*(θ:ℝ)-1)
    (U : Set X) (hmid : ∀ t∈Set.Icc α 1,p t∈U)
    (hlast : ∀ t,p₁ t∈U) :
    (∀ t∈Set.Icc θ 1,((p₀.trans p).trans p₁) t∈U) ∧
      ((p₀.trans p).trans p₁) θ=p α ∧
      ((p₀.trans p).trans p₁) 1=p₁ 1 := by
  obtain ⟨htail,hcenter⟩ := actual_three_piece_connector_exact_affine_tail_clocks p₀ p p₁
  have hθ : ((p₀.trans p).trans p₁) θ=p α := by
    rw [hcenter θ hθlo hθhi,←hα]
    exact Path.extend_apply p α.property
  refine ⟨?_,hθ,?_⟩
  · intro t ht
    by_cases hhalf : (t:ℝ)≤1/2
    · have htlo : 1/4≤(t:ℝ) := hθlo.trans ht.1
      rw [hcenter t htlo hhalf]
      let u : Interval := ⟨4*(t:ℝ)-1,by constructor <;> linarith⟩
      have hu : u∈Set.Icc α 1 := by
        constructor
        · change (α:ℝ)≤4*(t:ℝ)-1
          rw [hα]
          have hθt : (θ:ℝ)≤(t:ℝ) := ht.1
          linarith
        · exact u.property.2
      exact (Path.extend_apply p u.property).symm ▸ hmid u hu
    · rw [htail t (le_of_lt (not_le.mp hhalf))]
      let u : Interval := ⟨2*(t:ℝ)-1,by constructor <;> linarith [t.property.2]⟩
      exact (Path.extend_apply p₁ u.property).symm ▸ hlast u
  · exact ((p₀.trans p).trans p₁).target.trans p₁.target.symm

private theorem actual_two_negative_rays_extend_regional_connector_with_exact_clocks
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F G : Set S) (hF : IsClosed F) (hG : G⊆frontier F)
    (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
    (hclear : ∀ t,(a t).val∉G)
    (r₀ r₁ : C(Interval,S))
    (hr₀ : Topology.IsEmbedding r₀) (hr₁ : Topology.IsEmbedding r₁)
    (hzero₀ : r₀ 0=(a 0).val) (hzero₁ : r₁ 0=(a 1).val)
    (hout : ∀ t : Interval,0<t → r₀ t∉F)
    (hin : ∀ t,r₁ t∈interior F)
    (htrace₀ : Set.range r₀∩Set.range (fun t => (a t).val)={(a 0).val})
    (htrace₁ : Set.range r₁∩Set.range (fun t => (a t).val)={(a 1).val})
    (hd : Disjoint (Set.range r₀) (Set.range r₁)) :
    ∃ r : C(Interval,S),Topology.IsEmbedding r ∧
      r 0=r₀ 1 ∧ r 1=r₁ 1 ∧ r 0∉F ∧ (∀ t,r t∉G) ∧
      Set.range r=(Set.range r₀ ∪ Set.range (fun t => (a t).val))∪Set.range r₁ ∧
      (∀ t : Interval,1/2≤(t:ℝ) → r t=
        (⟨r₁,rfl,rfl⟩ : Path (r₁ 0) (r₁ 1)).extend (2*(t:ℝ)-1)) ∧
      (∀ t : Interval,1/4≤(t:ℝ) → (t:ℝ)≤1/2 → r t=
        (⟨⟨fun u => (a u).val,continuous_subtype_val.comp a.continuous⟩,rfl,rfl⟩ :
          Path (a 0).val (a 1).val).extend (4*(t:ℝ)-1)) := by
  let p₀ : Path (a 0).val (r₀ 1) :=
    { toContinuousMap := r₀
      source' := hzero₀
      target' := rfl }
  let p : Path (a 0).val (a 1).val :=
    { toContinuousMap := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
      source' := rfl
      target' := rfl }
  let p₁ : Path (a 1).val (r₁ 1) :=
    { toContinuousMap := r₁
      source' := hzero₁
      target' := rfl }
  have hp₀ : Function.Injective p₀ := hr₀.injective
  have hp : Function.Injective p :=
    fun s t h => ha.injective (Subtype.ext h)
  have hp₁ : Function.Injective p₁ := hr₁.injective
  have hranges : Set.range p₀.symm=Set.range r₀ := Path.symm_range p₀
  have hfirst : Set.range p₀.symm∩Set.range p={(a 0).val} := by
    rw [hranges]
    exact htrace₀
  have hfirstinj := actual_simple_path_concat p₀.symm p
    (hp₀.comp unitInterval.symm_involutive.injective) hp hfirst
  have hlast : Set.range (p₀.symm.trans p)∩Set.range p₁={(a 1).val} := by
    rw [Path.trans_range,Set.union_inter_distrib_right,hranges]
    have he : Set.range r₀∩Set.range r₁=∅ := Set.disjoint_iff_inter_eq_empty.mp hd
    have hpint : Set.range p∩Set.range p₁={(a 1).val} := by
      rw [Set.inter_comm]
      exact htrace₁
    have he' : Set.range r₀∩Set.range p₁=∅ := he
    rw [he',hpint,Set.empty_union]
  let P := (p₀.symm.trans p).trans p₁
  have hPi := actual_simple_path_concat (p₀.symm.trans p) p₁ hfirstinj hp₁ hlast
  let r : C(Interval,S) := ⟨P.toFun,P.continuous⟩
  have hrrange : Set.range r=(Set.range r₀∪Set.range (fun t => (a t).val))∪Set.range r₁ := by
    change Set.range P=_
    rw [Path.trans_range,Path.trans_range,hranges]
    rfl
  have hrclear : ∀ t,r t∉G := by
    intro t hg
    have hm := hrrange ▸ (Set.mem_range_self t : r t∈Set.range r)
    rcases hm with (⟨u,hu⟩ | ⟨u,hu⟩) | ⟨u,hu⟩
    · rw [←hu] at hg
      by_cases hu0 : u=0
      · exact hclear 0 (by simpa only [hu0,hzero₀] using hg)
      · exact hout u (bot_lt_iff_ne_bot.mpr hu0) (hF.frontier_subset (hG hg))
    · change (a u).val=r t at hu
      rw [←hu] at hg
      exact hclear u hg
    · rw [←hu] at hg
      exact Set.disjoint_left.mp disjoint_interior_frontier (hin u) (hG hg)
  obtain ⟨htail,hmid⟩ := actual_three_piece_connector_exact_affine_tail_clocks p₀.symm p p₁
  refine ⟨r,(r.continuous.isClosedEmbedding hPi).isEmbedding,
    P.source,P.target,?_,hrclear,hrrange,htail,hmid⟩
  exact (P.source.symm ▸ hout 1 (by norm_num))

private theorem actual_negative_terminal_chart_ray_with_signed_coordinates
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F C : Set S) (a : C(Interval,↥F))
    (N : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ)
    (hp : (a 1).val∈N.source) (hzero : N (a 1).val=0)
    (hη : 0<η) (htarget : Schoenflies.Plane.openSquare 0 η⊆N.target)
    (hlocal : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
      y∈interior F ∧
      (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
      (y∈C ↔ N y 0=0)) :
    ∃ r : C(Interval,S),Topology.IsEmbedding r ∧ r 0=(a 1).val ∧
      (∀ t,r t∈interior F) ∧
      (∀ t : Interval,0<t → r t∉C) ∧
      Set.range r ∩ Set.range (fun t => (a t).val)={(a 1).val} ∧
      (∀ t,r t∈N.symm '' Schoenflies.Plane.openSquare 0 η) ∧
      (∀ t,N (r t) 0=-(η/2)*(t:ℝ)) ∧ (∀ t,N (r t) 1=0) := by
  let v : Schoenflies.Plane := Schoenflies.Plane.mk (-η/2) 0
  have hvneg : v 0<0 := by dsimp [v];linarith
  have hvne : v≠0 := by
    intro he
    have : v 0=0 := by rw [he];rfl
    linarith
  have hv : v∈Schoenflies.Plane.openSquare 0 η := by
    change max |(-η/2)-0| |(0:ℝ)-0|<η
    rw [sub_zero,sub_zero,abs_of_neg (show -η/2<0 by linarith),abs_zero,max_eq_left (by linarith)]
    linarith
  have h0 : (0:Schoenflies.Plane)∈Schoenflies.Plane.openSquare 0 η := by
    simp [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,hη]
  let f : C(Interval,Schoenflies.Plane) := ⟨fun t => (t:ℝ) • v,by fun_prop⟩
  have hf : ∀ t,f t∈Schoenflies.Plane.openSquare 0 η := by
    intro t
    have hc := Schoenflies.Plane.convex_openSquare 0 η h0 hv
      (sub_nonneg.mpr t.property.2) t.property.1
      (by ring : (1-(t:ℝ))+(t:ℝ)=1)
    simpa [f] using hc
  let r : C(Interval,S) := ⟨fun t => N.symm (f t),
    N.continuousOn_symm.comp_continuous f.continuous (fun t => htarget (hf t))⟩
  have hr0 : r 0=(a 1).val := by
    change N.symm ((0:ℝ) • v)=(a 1).val
    rw [zero_smul,←hzero,N.left_inv hp]
  have hri : Function.Injective r := by
    intro t s he
    have hfs := N.symm.injOn (htarget (hf t)) (htarget (hf s)) he
    exact Subtype.ext ((smul_left_injective ℝ hvne) hfs)
  have hrpatch : ∀ t,r t∈N.symm '' Schoenflies.Plane.openSquare 0 η :=
    fun t => ⟨f t,hf t,rfl⟩
  have hrcoord : ∀ t,N (r t) 0=(t:ℝ)*v 0 := by
    intro t
    change N (N.symm (f t)) 0=(t:ℝ)*v 0
    rw [N.right_inv (htarget (hf t))]
    rfl
  have hrneg : ∀ t : Interval,0<t → N (r t) 0<0 := by
    intro t ht
    rw [hrcoord]
    exact mul_neg_of_pos_of_neg (show 0<(t:ℝ) from ht) hvneg
  have hrC : ∀ t : Interval,0<t → r t∉C := by
    intro t ht hin
    have he := (hlocal (r t) (hrpatch t)).2.2.mp hin
    exact (ne_of_lt (hrneg t ht)) he
  refine ⟨r,(r.continuous.isClosedEmbedding hri).isEmbedding,hr0,
    fun t => (hlocal _ (hrpatch t)).1,hrC,?_,hrpatch,?_,?_⟩
  · ext y
    constructor
    · rintro ⟨⟨t,ht⟩,ha⟩
      have ht0 : t=0 := by
        by_contra hn
        have hpos := ((hlocal _ (hrpatch t)).2.1.mp (ht.symm ▸ ha)).1
        exact (not_le_of_gt (hrneg t (bot_lt_iff_ne_bot.mpr hn))) hpos
      simpa only [ht0,hr0,Set.mem_singleton_iff] using ht.symm
    · intro hy
      have he : y=(a 1).val := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨⟨0,hr0⟩,⟨1,rfl⟩⟩
  · intro t
    rw [hrcoord]
    dsimp [v]
    ring
  · intro t
    change N (N.symm (f t)) 1=0
    rw [N.right_inv (htarget (hf t))]
    change (t:ℝ)*v 1=0
    simp [v]

private theorem actual_strip_compact_center_interval_uniform_clearance
    {X : Type} [TopologicalSpace X]
    (E : C(Interval × ↥(Set.Icc (-1 : ℝ) 1), X))
    (K : Set Interval) (hK : IsCompact K) (U : Set X) (hU : IsOpen U)
    (hcenter : ∀ t∈K,E (t,⟨0,by norm_num⟩)∈U) :
    ∃ δ : ℝ,0<δ ∧ δ<1 ∧
      ∀ t∈K,∀ w : ↥(Set.Icc (-1 : ℝ) 1), |(w:ℝ)|≤δ → E (t,w)∈U := by
  let zero : ↥(Set.Icc (-1 : ℝ) 1) := ⟨0,by norm_num⟩
  let L : Set (Interval × ↥(Set.Icc (-1 : ℝ) 1)) := K ×ˢ {zero}
  have hL : IsCompact L := hK.prod isCompact_singleton
  have hsub : L ⊆ E ⁻¹' U := by
    rintro ⟨t,w⟩ ⟨ht,hw⟩
    have hw' : w=zero := Set.mem_singleton_iff.mp hw
    subst w
    exact hcenter t ht
  obtain ⟨ε,hε,hεU⟩ := hL.exists_cthickening_subset_open (hU.preimage E.continuous) hsub
  refine ⟨min ε (1/2),lt_min hε (by norm_num),(min_le_right _ _).trans_lt (by norm_num),?_⟩
  intro t ht w hw
  apply hεU
  apply Metric.mem_cthickening_of_dist_le (t,w) (t,zero) ε L
    (show (t,zero)∈L from ⟨ht,rfl⟩)
  have hd : dist (t,w) (t,zero)=|(w:ℝ)| := by
    simp [Prod.dist_eq,Subtype.dist_eq,zero]
  rw [hd]
  exact hw.trans (min_le_left _ _)

private theorem actual_small_strip_widths_cross_terminal_chart_axis
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F C : Set S) (hF : IsClosed F)
    (E : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S))
    (N : OpenPartialHomeomorph S Schoenflies.Plane)
    (U : Set S) (hU : IsOpen U) (hUN : U⊆N.source)
    (θ : Interval)
    (hstart : E (0,⟨0,by norm_num⟩)∉F)
    (htail : ∀ t∈Set.Icc θ 1,E (t,⟨0,by norm_num⟩)∈U)
    (hpositive : 0<N (E (θ,⟨0,by norm_num⟩)) 0)
    (hnegative : N (E (1,⟨0,by norm_num⟩)) 0<0)
    (haxis : ∀ y∈U,N y 0=0 → y∈C) :
    ∃ δ : ℝ,0<δ ∧ δ<1 ∧
      ∀ w : ↥(Set.Icc (-1 : ℝ) 1), |(w:ℝ)|≤δ →
        E (0,w)∉F ∧ ∃ t,E (t,w)∈C := by
  let Vpos : Set S := U ∩ N ⁻¹' {v : Schoenflies.Plane | 0<v 0}
  let Vneg : Set S := U ∩ N ⁻¹' {v : Schoenflies.Plane | v 0<0}
  have hcoord : Continuous (fun v : Schoenflies.Plane => v 0) := by fun_prop
  have hposOpen : IsOpen Vpos := by
    have hopen : IsOpen {v : Schoenflies.Plane | 0<v 0} := isOpen_lt continuous_const hcoord
    have h := N.isOpen_inter_preimage hopen
    have he : Vpos=U∩(N.source∩N ⁻¹' {v : Schoenflies.Plane | 0<v 0}) := by
      ext y
      exact ⟨fun hy => ⟨hy.1,hUN hy.1,hy.2⟩,fun hy => ⟨hy.1,hy.2.2⟩⟩
    rw [he]
    exact hU.inter h
  have hnegOpen : IsOpen Vneg := by
    have hopen : IsOpen {v : Schoenflies.Plane | v 0<0} := isOpen_lt hcoord continuous_const
    have h := N.isOpen_inter_preimage hopen
    have he : Vneg=U∩(N.source∩N ⁻¹' {v : Schoenflies.Plane | v 0<0}) := by
      ext y
      exact ⟨fun hy => ⟨hy.1,hUN hy.1,hy.2⟩,fun hy => ⟨hy.1,hy.2.2⟩⟩
    rw [he]
    exact hU.inter h
  obtain ⟨δ₀,hδ₀,_,houtside⟩ := actual_strip_compact_center_interval_uniform_clearance
    E {0} isCompact_singleton Fᶜ hF.isOpen_compl
    (by intro t ht;have he : t=0 := ht;subst t;exact hstart)
  obtain ⟨δT,hδT,_,hwhole⟩ := actual_strip_compact_center_interval_uniform_clearance
    E (Set.Icc θ 1) isCompact_Icc U hU htail
  obtain ⟨δP,hδP,_,hpos⟩ := actual_strip_compact_center_interval_uniform_clearance
    E {θ} isCompact_singleton Vpos hposOpen
    (by intro t ht;subst t;exact ⟨htail θ ⟨le_rfl,le_top⟩,hpositive⟩)
  obtain ⟨δN,hδN,_,hneg⟩ := actual_strip_compact_center_interval_uniform_clearance
    E {1} isCompact_singleton Vneg hnegOpen
    (by intro t ht;subst t;exact ⟨htail 1 ⟨le_top,le_rfl⟩,hnegative⟩)
  let δ := min (min δ₀ δT) (min δP (min δN (1/2)))
  have hδ : 0<δ := lt_min (lt_min hδ₀ hδT) (lt_min hδP (lt_min hδN (by norm_num)))
  have hδ₀' : δ≤δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hδT' : δ≤δT := (min_le_left _ _).trans (min_le_right _ _)
  have hδP' : δ≤δP := (min_le_right _ _).trans (min_le_left _ _)
  have hδN' : δ≤δN := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδhalf : δ≤1/2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨δ,hδ,hδhalf.trans_lt (by norm_num),?_⟩
  intro w hw
  refine ⟨houtside 0 rfl w (hw.trans hδ₀'),?_⟩
  let clock : C(Interval,Interval) := {
    toFun := fun t => ⟨(θ:ℝ)+(1-(θ:ℝ))*(t:ℝ),by
      constructor <;> nlinarith [θ.property.1,θ.property.2,t.property.1,t.property.2]⟩
    continuous_toFun := by fun_prop }
  have hc0 : clock 0=θ := Subtype.ext (by change (θ:ℝ)+(1-(θ:ℝ))*0=(θ:ℝ);ring)
  have hc1 : clock 1=1 := Subtype.ext (by change (θ:ℝ)+(1-(θ:ℝ))*1=1;ring)
  have hcK : ∀ t,clock t∈Set.Icc θ 1 := by
    intro t
    constructor
    · change (θ:ℝ)≤(θ:ℝ)+(1-(θ:ℝ))*(t:ℝ)
      nlinarith [θ.property.2,t.property.1]
    · exact (clock t).property.2
  let q : C(Interval,S) := ⟨fun t => E (clock t,w),by fun_prop⟩
  have hqU : ∀ t,q t∈U := fun t => hwhole (clock t) (hcK t) w (hw.trans hδT')
  let f : C(Interval,ℝ) := ⟨fun t => N (q t) 0,
    hcoord.comp (N.continuousOn.comp_continuous q.continuous
      (fun t => hUN (hqU t)))⟩
  have hf0 : 0≤f 0 := by
    change 0≤N (E (clock 0,w)) 0
    rw [hc0]
    exact (hpos θ rfl w (hw.trans hδP')).2.le
  have hf1 : f 1≤0 := by
    change N (E (clock 1,w)) 0≤0
    rw [hc1]
    exact (hneg 1 rfl w (hw.trans hδN')).2.le
  obtain ⟨t,ht⟩ := intermediate_value_univ 1 0 f.continuous ⟨hf1,hf0⟩
  exact ⟨clock t,haxis (q t) (hqU t) ht⟩

private theorem actual_embedded_outside_track_regional_first_curve_segment
    {X : Type} [TopologicalSpace X] [T2Space X]
    (F B G C : Set X) (hF : IsClosed F) (hC : IsClosed C)
    (hCi : C⊆interior F) (hfront : frontier F⊆B∪G)
    (q : C(Interval,X)) (hq : Topology.IsEmbedding q)
    (hq0 : q 0∉F) (hclear : ∀ t,q t∉G)
    (hmeet : ∃ t,q t∈C) :
    ∃ (p : C(Interval,↥F)) (clock : C(Interval,Interval)),
      Topology.IsEmbedding p ∧ Topology.IsEmbedding clock ∧
      (∀ t,(p t).val=q (clock t)) ∧
      (p 0).val∈B ∧
      (∀ t : Interval,0<t → (p t).val∈interior F) ∧
      (∀ t,(p t).val∈C ↔ t=1) ∧
      Set.range (fun t => (p t).val)⊆Set.range q := by
  let T : Set Interval := q ⁻¹' C
  have hT : IsCompact T := (hC.preimage q.continuous).isCompact
  obtain ⟨τ,hτ,hmin⟩ := hT.exists_isLeast hmeet
  have hτi : q τ∈interior F := hCi hτ
  let Z : Set Interval := Set.Icc 0 τ ∩ q ⁻¹' (interior F)ᶜ
  have hZ : IsCompact Z :=
    (isClosed_Icc.inter (isOpen_interior.isClosed_compl.preimage q.continuous)).isCompact
  have hZne : Z.Nonempty := ⟨0,⟨⟨le_rfl,bot_le⟩,fun hi => hq0 (interior_subset hi)⟩⟩
  obtain ⟨σ,hσ,hmax⟩ := hZ.exists_isGreatest hZne
  have hστ : σ<τ := lt_of_le_of_ne hσ.1.2 (fun he => hσ.2 (he.symm ▸ hτi))
  let clock : C(Interval,Interval) := {
    toFun := fun t => ⟨(σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ),by
      constructor <;> nlinarith [σ.property.1,σ.property.2,τ.property.1,
        τ.property.2,t.property.1,t.property.2,(show (σ:ℝ)<(τ:ℝ) from hστ)]⟩
    continuous_toFun := by fun_prop }
  have hc0 : clock 0=σ := Subtype.ext (by change (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*0=(σ:ℝ);ring)
  have hc1 : clock 1=τ := Subtype.ext (by change (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*1=(τ:ℝ);ring)
  have hclockinj : Function.Injective clock := by
    intro t u he
    have hev := congrArg Subtype.val he
    have hp : 0<(τ:ℝ)-(σ:ℝ) := sub_pos.mpr hστ
    apply Subtype.ext
    change (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ)=
      (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(u:ℝ) at hev
    nlinarith
  let r : C(Interval,X) := q.comp clock
  have hrI (t : Interval) (ht : 0<t) : r t∈interior F := by
    by_contra hn
    have hσc : σ<clock t := by
      change (σ:ℝ)<(σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ)
      have hp : 0<(τ:ℝ)-(σ:ℝ) := sub_pos.mpr hστ
      have htR : 0<(t:ℝ) := ht
      nlinarith
    have hcτ : clock t≤τ := by
      change (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ)≤(τ:ℝ)
      nlinarith [t.property.2,(show (σ:ℝ)<(τ:ℝ) from hστ)]
    have hcZ : clock t∈Z := ⟨⟨bot_le,hcτ⟩,hn⟩
    exact (not_le_of_gt hσc) (hmax hcZ)
  have h0cl : (0 : Interval)∈closure (Set.Ioo (0 : Interval) 1) := by
    rw [closure_Ioo (by norm_num : (0 : Interval)≠1)]
    exact ⟨le_rfl,bot_le⟩
  have hr0F : r 0∈F := by
    have hr0cl : r 0∈closure (r '' Set.Ioo (0 : Interval) 1) :=
      mem_closure_image r.continuous.continuousAt h0cl
    apply closure_minimal (s := r '' Set.Ioo (0 : Interval) 1) (t := F) _ hF hr0cl
    rintro y ⟨t,ht,rfl⟩
    exact interior_subset (hrI t ht.1)
  have hrF (t : Interval) : r t∈F := by
    by_cases ht : t=0
    · simpa only [ht] using hr0F
    · exact interior_subset (hrI t (bot_lt_iff_ne_bot.mpr ht))
  let p : C(Interval,↥F) := ⟨fun t => ⟨r t,hrF t⟩,r.continuous.subtype_mk _⟩
  have hp : Topology.IsEmbedding p := (hq.comp
    (clock.continuous.isClosedEmbedding hclockinj).isEmbedding).codRestrict _ hrF
  have hr0front : r 0∈frontier F := by
    apply (mem_frontier_iff_notMem_interior hr0F).mpr
    change q (clock 0)∉interior F
    rw [hc0]
    exact hσ.2
  have hr0B : r 0∈B := (hfront hr0front).resolve_right (hclear (clock 0))
  refine ⟨p,clock,hp,(clock.continuous.isClosedEmbedding hclockinj).isEmbedding,
    fun _ => rfl,hr0B,hrI,?_,?_⟩
  · intro t
    constructor
    · intro htC
      have htmin : τ≤clock t := hmin htC
      apply Subtype.ext
      change (t:ℝ)=1
      change (τ:ℝ)≤(σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ) at htmin
      nlinarith [t.property.2,(show (σ:ℝ)<(τ:ℝ) from hστ)]
    · intro ht
      subst t
      change q (clock 1)∈C
      rw [hc1]
      exact hτ
  · rintro y ⟨t,rfl⟩
    exact ⟨clock t,rfl⟩

private theorem actual_two_disjoint_outside_tracks_regional_first_curve_segments
    {X : Type} [TopologicalSpace X] [T2Space X]
    (F B G C : Set X) (hF : IsClosed F) (hC : IsClosed C)
    (hCi : C⊆interior F) (hfront : frontier F⊆B∪G)
    (q₀ q₁ : C(Interval,X)) (hq₀ : Topology.IsEmbedding q₀)
    (hq₁ : Topology.IsEmbedding q₁)
    (hstart₀ : q₀ 0∉F) (hstart₁ : q₁ 0∉F)
    (hclear₀ : ∀ t,q₀ t∉G) (hclear₁ : ∀ t,q₁ t∉G)
    (hmeet₀ : ∃ t,q₀ t∈C) (hmeet₁ : ∃ t,q₁ t∈C)
    (hdisjoint : Disjoint (Set.range q₀) (Set.range q₁)) :
    ∃ p₀ p₁ : C(Interval,↥F),
      Topology.IsEmbedding p₀ ∧ Topology.IsEmbedding p₁ ∧
      (p₀ 0).val∈B ∧ (p₁ 0).val∈B ∧
      (∀ t : Interval,0<t → (p₀ t).val∈interior F) ∧
      (∀ t : Interval,0<t → (p₁ t).val∈interior F) ∧
      (∀ t,(p₀ t).val∈C ↔ t=1) ∧
      (∀ t,(p₁ t).val∈C ↔ t=1) ∧
      Disjoint (Set.range (fun t => (p₀ t).val))
        (Set.range (fun t => (p₁ t).val)) := by
  obtain ⟨p₀,clock₀,hp₀,_,_,hB₀,hI₀,hC₀,hr₀⟩ :=
    actual_embedded_outside_track_regional_first_curve_segment
      F B G C hF hC hCi hfront q₀ hq₀ hstart₀ hclear₀ hmeet₀
  obtain ⟨p₁,clock₁,hp₁,_,_,hB₁,hI₁,hC₁,hr₁⟩ :=
    actual_embedded_outside_track_regional_first_curve_segment
      F B G C hF hC hCi hfront q₁ hq₁ hstart₁ hclear₁ hmeet₁
  exact ⟨p₀,p₁,hp₀,hp₁,hB₀,hB₁,hI₀,hI₁,hC₀,hC₁,hdisjoint.mono hr₀ hr₁⟩

private theorem actual_terminal_chart_crossing_strip_constructs_disjoint_regional_rails
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B G C : Set S) (hF : IsClosed F) (hC : IsClosed C)
    (hCi : C⊆interior F) (hfront : frontier F⊆B∪G)
    (E : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S))
    (hE : Topology.IsEmbedding E) (hclear : ∀ z,E z∉G)
    (N : OpenPartialHomeomorph S Schoenflies.Plane)
    (U : Set S) (hU : IsOpen U) (hUN : U⊆N.source)
    (θ : Interval)
    (hstart : E (0,⟨0,by norm_num⟩)∉F)
    (htail : ∀ t∈Set.Icc θ 1,E (t,⟨0,by norm_num⟩)∈U)
    (hpositive : 0<N (E (θ,⟨0,by norm_num⟩)) 0)
    (hnegative : N (E (1,⟨0,by norm_num⟩)) 0<0)
    (haxis : ∀ y∈U,N y 0=0 → y∈C) :
    ∃ p₀ p₁ : C(Interval,↥F),
      Topology.IsEmbedding p₀ ∧ Topology.IsEmbedding p₁ ∧
      (p₀ 0).val∈B ∧ (p₁ 0).val∈B ∧
      (∀ t : Interval,0<t → (p₀ t).val∈interior F) ∧
      (∀ t : Interval,0<t → (p₁ t).val∈interior F) ∧
      (∀ t,(p₀ t).val∈C ↔ t=1) ∧
      (∀ t,(p₁ t).val∈C ↔ t=1) ∧
      Disjoint (Set.range (fun t => (p₀ t).val))
        (Set.range (fun t => (p₁ t).val)) := by
  obtain ⟨δ,hδ,hδ1,hwidth⟩ := actual_small_strip_widths_cross_terminal_chart_axis
    F C hF E N U hU hUN θ hstart htail hpositive hnegative haxis
  let w₀ : ↥(Set.Icc (-1 : ℝ) 1) := ⟨-δ/2,by constructor <;> linarith⟩
  let w₁ : ↥(Set.Icc (-1 : ℝ) 1) := ⟨δ/2,by constructor <;> linarith⟩
  have hw₀ : |(w₀:ℝ)|≤δ := by
    change |-δ/2|≤δ
    rw [abs_of_neg (by linarith)]
    linarith
  have hw₁ : |(w₁:ℝ)|≤δ := by
    change |δ/2|≤δ
    rw [abs_of_pos (by linarith)]
    linarith
  have hwne : w₀≠w₁ := by
    intro he
    have hev := congrArg Subtype.val he
    change -δ/2=δ/2 at hev
    linarith
  let q₀ : C(Interval,S) := ⟨fun t => E (t,w₀),by fun_prop⟩
  let q₁ : C(Interval,S) := ⟨fun t => E (t,w₁),by fun_prop⟩
  have hq₀ : Topology.IsEmbedding q₀ :=
    (q₀.continuous.isClosedEmbedding (fun s t h => congrArg Prod.fst (hE.injective h))).isEmbedding
  have hq₁ : Topology.IsEmbedding q₁ :=
    (q₁.continuous.isClosedEmbedding (fun s t h => congrArg Prod.fst (hE.injective h))).isEmbedding
  have hd : Disjoint (Set.range q₀) (Set.range q₁) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨s,hs⟩ ⟨t,ht⟩
    exact hwne (congrArg Prod.snd (hE.injective (hs.trans ht.symm)))
  exact actual_two_disjoint_outside_tracks_regional_first_curve_segments
    F B G C hF hC hCi hfront q₀ q₁ hq₀ hq₁
    (hwidth w₀ hw₀).1 (hwidth w₁ hw₁).1
    (fun t => hclear (t,w₀)) (fun t => hclear (t,w₁))
    (hwidth w₀ hw₀).2 (hwidth w₁ hw₁).2 hd

private theorem actual_continuous_arc_terminal_open_patch_closed_tail
    {X : Type} [TopologicalSpace X]
    (a : C(Interval,X)) (U : Set X) (hU : IsOpen U) (ha1 : a 1∈U) :
    ∃ α : Interval,0<(α:ℝ) ∧ (α:ℝ)<1 ∧
      ∀ t∈Set.Icc α 1,a t∈U := by
  have hopen : IsOpen (a ⁻¹' U) := hU.preimage a.continuous
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen 1 ha1
  let δ := min ε 1 / 2
  have hδ : 0<δ := half_pos (lt_min hε (by norm_num))
  have hδε : δ<ε := (half_lt_self (lt_min hε (by norm_num))).trans_le (min_le_left _ _)
  have hδhalf : δ≤1/2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let α : Interval := ⟨1-δ,by constructor <;> linarith⟩
  refine ⟨α,by change 0<1-δ;linarith,by change 1-δ<1;linarith,?_⟩
  intro t ht
  apply hball
  change dist t (1 : Interval)<ε
  rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (by exact sub_nonpos.mpr t.property.2)]
  have hαt : 1-δ≤(t:ℝ) := ht.1
  change -((t:ℝ)-1)<ε
  linarith

private theorem actual_terminal_chart_clean_connector_positive_precontact
    {S : Type} [TopologicalSpace S]
    (a : C(Interval,S)) (C U : Set S)
    (N : OpenPartialHomeomorph S Schoenflies.Plane)
    (hU : IsOpen U) (haU : a 1∈U)
    (hcontact : ∀ t,a t∈C ↔ t=1)
    (hlocal : ∀ y∈U,
      (y∈Set.range a ↔ 0≤N y 0 ∧ N y 1=0) ∧ (y∈C ↔ N y 0=0)) :
    ∃ α : Interval,0<(α:ℝ) ∧ (α:ℝ)<1 ∧
      (∀ t∈Set.Icc α 1,a t∈U) ∧ 0<N (a α) 0 := by
  obtain ⟨α,hα0,hα1,htail⟩ :=
    actual_continuous_arc_terminal_open_patch_closed_tail a U hU haU
  have hαU : a α∈U := htail α ⟨le_rfl,le_top⟩
  have hnonneg : 0≤N (a α) 0 :=
    ((hlocal _ hαU).1.mp (Set.mem_range_self α)).1
  have hne : N (a α) 0≠0 := by
    intro he
    have hαC : a α∈C := (hlocal _ hαU).2.mpr he
    have he1 : α=1 := (hcontact α).mp hαC
    have : (α:ℝ)=1 := congrArg Subtype.val he1
    linarith
  exact ⟨α,hα0,hα1,htail,lt_of_le_of_ne hnonneg hne.symm⟩

private theorem actual_mixed_clean_connector_constructs_two_regional_proper_rails
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Schoenflies.Plane S]
    (F B G C : Set S) (hF : IsClosed F) (hC : IsClosed C) (hGclosed : IsClosed G)
    (hCi : C⊆interior F) (hGfront : G⊆frontier F) (hfront : frontier F⊆B∪G)
    (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
    (ha0front : (a 0).val∈frontier F)
    (hclear : ∀ t,(a t).val∉G) (hcircle : ∀ t,(a t).val∈C ↔ t=1)
    (N₀ N₁ : OpenPartialHomeomorph S Schoenflies.Plane) (η₀ η₁ : ℝ)
    (hp₀ : (a 0).val∈N₀.source) (hz₀ : N₀ (a 0).val=0)
    (hη₀ : 0<η₀) (ht₀ : Schoenflies.Plane.openSquare 0 η₀⊆N₀.target)
    (hl₀ : ∀ y∈N₀.symm '' Schoenflies.Plane.openSquare 0 η₀,y∈F ↔ 0≤N₀ y 0)
    (hp₁ : (a 1).val∈N₁.source) (hz₁ : N₁ (a 1).val=0)
    (hη₁ : 0<η₁) (ht₁ : Schoenflies.Plane.openSquare 0 η₁⊆N₁.target)
    (hl₁ : ∀ y∈N₁.symm '' Schoenflies.Plane.openSquare 0 η₁,
      y∈interior F ∧
      (y∈Set.range (fun t => (a t).val) ↔ 0≤N₁ y 0 ∧ N₁ y 1=0) ∧
      (y∈C ↔ N₁ y 0=0)) :
    ∃ p₀ p₁ : C(Interval,↥F),
      Topology.IsEmbedding p₀ ∧ Topology.IsEmbedding p₁ ∧
      (p₀ 0).val∈B ∧ (p₁ 0).val∈B ∧
      (∀ t : Interval,0<t → (p₀ t).val∈interior F) ∧
      (∀ t : Interval,0<t → (p₁ t).val∈interior F) ∧
      (∀ t,(p₀ t).val∈C ↔ t=1) ∧
      (∀ t,(p₁ t).val∈C ↔ t=1) ∧
      Disjoint (Set.range (fun t => (p₀ t).val))
        (Set.range (fun t => (p₁ t).val)) := by
  obtain ⟨r₀,hr₀,hzR₀,hoR₀,htR₀,_⟩ :=
    actual_negative_chart_halfplane_ray_from_positive_square F a N₀ η₀ hp₀ hz₀ hη₀ ht₀ hl₀
  obtain ⟨r₁,hr₁,hzR₁,hiR₁,_,htR₁,hpatchR₁,hcoordR₁,_⟩ :=
    actual_negative_terminal_chart_ray_with_signed_coordinates F C a N₁ η₁ hp₁ hz₁ hη₁ ht₁ hl₁
  have hd : Disjoint (Set.range r₀) (Set.range r₁) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t,ht⟩ ⟨u,hu⟩
    have hi : r₀ t∈interior F := ht ▸ hu.symm ▸ hiR₁ u
    by_cases ht0 : t=0
    · have h0i : (a 0).val∈interior F := by simpa only [ht0,hzR₀] using hi
      exact Set.disjoint_left.mp disjoint_interior_frontier h0i ha0front
    · exact hoR₀ t (bot_lt_iff_ne_bot.mpr ht0) (interior_subset hi)
  obtain ⟨r,hr,hr0,hr1,hrout,hrclear,_,hrtail,hrmid⟩ :=
    actual_two_negative_rays_extend_regional_connector_with_exact_clocks
      F G hF hGfront a ha hclear r₀ r₁ hr₀ hr₁ hzR₀ hzR₁ hoR₀ hiR₁ htR₀ htR₁ hd
  obtain ⟨E,hE,hcenter,hEU⟩ := source_whole_embedded_arc_strip r hr Gᶜ hGclosed.isOpen_compl
    (by rintro y ⟨t,rfl⟩;exact hrclear t)
  let EE : C(Interval × Set.Icc (-1 : ℝ) 1,S) := ⟨E,hE.continuous⟩
  let U : Set S := N₁.symm '' Schoenflies.Plane.openSquare 0 η₁
  have hU : IsOpen U := N₁.symm.isOpen_image_of_subset_source
    (Schoenflies.Plane.isOpen_openSquare 0 η₁) ht₁
  have hUN : U⊆N₁.source := by
    rintro y ⟨v,hv,rfl⟩
    exact N₁.map_target (ht₁ hv)
  let aa : C(Interval,S) := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
  have ha1U : aa 1∈U := by
    refine ⟨0,?_,?_⟩
    · simp [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,hη₁]
    · change N₁.symm 0=(a 1).val
      rw [←hz₁,N₁.left_inv hp₁]
  obtain ⟨α,hα0,hα1,hαtail,hαpos⟩ :=
    actual_terminal_chart_clean_connector_positive_precontact aa C U N₁ hU ha1U hcircle
      (fun y hy => (hl₁ y hy).2)
  let θ : Interval := ⟨((α:ℝ)+1)/4,by constructor <;> linarith [α.property.1,α.property.2]⟩
  have hθlo : 1/4≤(θ:ℝ) := by change 1/4≤((α:ℝ)+1)/4;linarith
  have hθhi : (θ:ℝ)≤1/2 := by change ((α:ℝ)+1)/4≤1/2;linarith
  have hαθ : (α:ℝ)=4*(θ:ℝ)-1 := by dsimp [θ];ring
  let p : Path (a 0).val (a 1).val := ⟨aa,rfl,rfl⟩
  let q : Path (r₁ 0) (r₁ 1) := ⟨r₁,rfl,rfl⟩
  have hrθ : r θ=aa α := by
    rw [hrmid θ hθlo hθhi,←hαθ]
    exact Path.extend_apply p α.property
  have hEtail : ∀ t∈Set.Icc θ 1,EE (t,⟨0,by norm_num⟩)∈U := by
    intro t ht
    change E (t,⟨0,by norm_num⟩)∈U
    rw [hcenter]
    by_cases hhalf : (t:ℝ)≤1/2
    · have htlo : 1/4≤(t:ℝ) := hθlo.trans ht.1
      rw [hrmid t htlo hhalf]
      let u : Interval := ⟨4*(t:ℝ)-1,by constructor <;> linarith⟩
      have huα : α≤u := by
        change (α:ℝ)≤4*(t:ℝ)-1
        rw [hαθ]
        have hθt : (θ:ℝ)≤(t:ℝ) := ht.1
        linarith
      exact (Path.extend_apply p u.property).symm ▸ hαtail u ⟨huα,le_top⟩
    · rw [hrtail t (le_of_lt (not_le.mp hhalf))]
      let u : Interval := ⟨2*(t:ℝ)-1,by constructor <;> linarith [t.property.2]⟩
      exact (Path.extend_apply q u.property).symm ▸ hpatchR₁ u
  have hEpositive : 0<N₁ (EE (θ,⟨0,by norm_num⟩)) 0 := by
    change 0<N₁ (E (θ,⟨0,by norm_num⟩)) 0
    rw [hcenter,hrθ]
    exact hαpos
  have hEnegative : N₁ (EE (1,⟨0,by norm_num⟩)) 0<0 := by
    change N₁ (E (1,⟨0,by norm_num⟩)) 0<0
    rw [hcenter,hr1,hcoordR₁]
    norm_num
    linarith
  exact actual_terminal_chart_crossing_strip_constructs_disjoint_regional_rails
    F B G C hF hC hCi hfront EE hE (fun z => hEU (Set.mem_range_self z))
    N₁ U hU hUN θ (by change E (0,⟨0,by norm_num⟩)∉F;rw [hcenter];exact hrout)
    hEtail hEpositive hEnegative (fun y hy hz => (hl₁ y hy).2.2.mpr hz)

private theorem actual_ambient_rectangle_boundary_relation_with_named_rails
    {X : Type} [TopologicalSpace X] {x₀ y₀ x₁ y₁ : X}
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,X))
    (p : Path x₀ x₁) (q : Path y₀ y₁)
    (hP : ∀ t,E (t,⟨1,by norm_num⟩)=p t)
    (hQ : ∀ t,E (t,⟨-1,by norm_num⟩)=q t) :
    ∃ (b₀ : Path x₀ y₀) (b₁ : Path x₁ y₁),
      (∀ t,b₀ t=E (0,⟨1-2*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩)) ∧
      (∀ t,b₁ t=E (1,⟨1-2*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩)) ∧
      (p.trans b₁).Homotopic (b₀.trans q) := by
    let : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    let : ContractibleSpace (Set.Icc (-1 : ℝ) 1) :=
      (convex_Icc (-1:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    let pd : Path ((0:Interval),(⟨1,by norm_num⟩ : Set.Icc (-1:ℝ) 1))
        ((1:Interval),(⟨1,by norm_num⟩ : Set.Icc (-1:ℝ) 1)) :=
      ⟨⟨fun t => (t,⟨1,by norm_num⟩),continuous_id.prodMk continuous_const⟩,rfl,rfl⟩
    let qd : Path ((0:Interval),(⟨-1,by norm_num⟩ : Set.Icc (-1:ℝ) 1))
        ((1:Interval),(⟨-1,by norm_num⟩ : Set.Icc (-1:ℝ) 1)) :=
      ⟨⟨fun t => (t,⟨-1,by norm_num⟩),continuous_id.prodMk continuous_const⟩,rfl,rfl⟩
    let k : C(Interval,Set.Icc (-1:ℝ) 1) := ⟨fun t => ⟨1-2*(t:ℝ),by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩,
      by fun_prop⟩
    let bd0 : Path ((0:Interval),(⟨1,by norm_num⟩ : Set.Icc (-1:ℝ) 1))
        ((0:Interval),(⟨-1,by norm_num⟩ : Set.Icc (-1:ℝ) 1)) :=
      ⟨⟨fun t => (0,k t),continuous_const.prodMk k.continuous⟩,
        Prod.ext rfl (Subtype.ext (by norm_num [k])),Prod.ext rfl (Subtype.ext (by norm_num [k]))⟩
    let bd1 : Path ((1:Interval),(⟨1,by norm_num⟩ : Set.Icc (-1:ℝ) 1))
        ((1:Interval),(⟨-1,by norm_num⟩ : Set.Icc (-1:ℝ) 1)) :=
      ⟨⟨fun t => (1,k t),continuous_const.prodMk k.continuous⟩,
        Prod.ext rfl (Subtype.ext (by norm_num [k])),Prod.ext rfl (Subtype.ext (by norm_num [k]))⟩
    have hEP₀ : E (0,⟨1,by norm_num⟩)=x₀ := (hP 0).trans p.source
    have hEP₁ : E (1,⟨1,by norm_num⟩)=x₁ := (hP 1).trans p.target
    have hEQ₀ : E (0,⟨-1,by norm_num⟩)=y₀ := (hQ 0).trans q.source
    have hEQ₁ : E (1,⟨-1,by norm_num⟩)=y₁ := (hQ 1).trans q.target
    have hk₀ : k 0=(⟨1,by norm_num⟩ : Set.Icc (-1:ℝ) 1) := Subtype.ext (by norm_num [k])
    have hk₁ : k 1=(⟨-1,by norm_num⟩ : Set.Icc (-1:ℝ) 1) := Subtype.ext (by norm_num [k])
    let b₀ : Path x₀ y₀ := {
      toFun := fun t => E (0,k t)
      continuous_toFun := E.continuous.comp (continuous_const.prodMk k.continuous)
      source' := by change E (0,k 0)=x₀;rw [hk₀];exact hEP₀
      target' := by change E (0,k 1)=y₀;rw [hk₁];exact hEQ₀ }
    let b₁ : Path x₁ y₁ := {
      toFun := fun t => E (1,k t)
      continuous_toFun := E.continuous.comp (continuous_const.prodMk k.continuous)
      source' := by change E (1,k 0)=x₁;rw [hk₀];exact hEP₁
      target' := by change E (1,k 1)=y₁;rw [hk₁];exact hEQ₁ }
    have H := (SimplyConnectedSpace.paths_homotopic (pd.trans bd1) (bd0.trans qd)).map E
    have H' := Path.Homotopic.pathCast H hEP₀.symm hEQ₁.symm
    have hleft : ((pd.trans bd1).map E.continuous).cast hEP₀.symm hEQ₁.symm=p.trans b₁ := by
      apply Path.ext
      funext t
      simp only [Path.cast_coe,Path.map_coe,Function.comp_apply,Path.trans_apply]
      by_cases ht : (t:ℝ)≤1/2
      · simp only [dite_eq_left ht]
        exact hP _
      · simp only [dite_eq_right ht]
        rfl
    have hright : ((bd0.trans qd).map E.continuous).cast hEP₀.symm hEQ₁.symm=b₀.trans q := by
      apply Path.ext
      funext t
      simp only [Path.cast_coe,Path.map_coe,Function.comp_apply,Path.trans_apply]
      by_cases ht : (t:ℝ)≤1/2
      · simp only [dite_eq_left ht]
        rfl
      · simp only [dite_eq_right ht]
        exact hQ _
    rw [hleft,hright] at H'
    exact ⟨b₀,b₁,fun _ => rfl,fun _ => rfl,H'⟩

private theorem actual_three_piece_connector_exact_affine_initial_clock
    {X : Type} [TopologicalSpace X]
    {x y z w : X} (p₀ : Path x y) (p : Path y z) (p₁ : Path z w) :
    ∀ t : Interval,(t:ℝ)≤1/4 →
      ((p₀.trans p).trans p₁) t=p₀.extend (4*(t:ℝ)) := by
  intro t ht
  rw [←Path.extend_apply,Path.extend_trans_of_le_half _ _ (by linarith : (t:ℝ)≤1/2),
    Path.extend_trans_of_le_half _ _ (by linarith : 2*(t:ℝ)≤1/2)]
  congr 1
  ring

private theorem actual_two_negative_rays_extend_regional_connector_with_three_exact_clocks
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F G : Set S) (hF : IsClosed F) (hG : G⊆frontier F)
    (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
    (hclear : ∀ t,(a t).val∉G)
    (r₀ r₁ : C(Interval,S))
    (hr₀ : Topology.IsEmbedding r₀) (hr₁ : Topology.IsEmbedding r₁)
    (hzero₀ : r₀ 0=(a 0).val) (hzero₁ : r₁ 0=(a 1).val)
    (hout : ∀ t : Interval,0<t → r₀ t∉F)
    (hin : ∀ t,r₁ t∈interior F)
    (htrace₀ : Set.range r₀∩Set.range (fun t => (a t).val)={(a 0).val})
    (htrace₁ : Set.range r₁∩Set.range (fun t => (a t).val)={(a 1).val})
    (hd : Disjoint (Set.range r₀) (Set.range r₁)) :
    ∃ r : C(Interval,S),Topology.IsEmbedding r ∧
      r 0=r₀ 1 ∧ r 1=r₁ 1 ∧ r 0∉F ∧ (∀ t,r t∉G) ∧
      Set.range r=(Set.range r₀ ∪ Set.range (fun t => (a t).val))∪Set.range r₁ ∧
      (∀ t : Interval,1/2≤(t:ℝ) → r t=
        (⟨r₁,rfl,rfl⟩ : Path (r₁ 0) (r₁ 1)).extend (2*(t:ℝ)-1)) ∧
      (∀ t : Interval,1/4≤(t:ℝ) → (t:ℝ)≤1/2 → r t=
        (⟨⟨fun u => (a u).val,continuous_subtype_val.comp a.continuous⟩,rfl,rfl⟩ :
          Path (a 0).val (a 1).val).extend (4*(t:ℝ)-1)) ∧
      (∀ t : Interval,(t:ℝ)≤1/4 → r t=
        (⟨r₀,rfl,rfl⟩ : Path (r₀ 0) (r₀ 1)).symm.extend (4*(t:ℝ))) := by
  let p₀ : Path (a 0).val (r₀ 1) :=
    { toContinuousMap := r₀
      source' := hzero₀
      target' := rfl }
  let p : Path (a 0).val (a 1).val :=
    { toContinuousMap := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
      source' := rfl
      target' := rfl }
  let p₁ : Path (a 1).val (r₁ 1) :=
    { toContinuousMap := r₁
      source' := hzero₁
      target' := rfl }
  have hp₀ : Function.Injective p₀ := hr₀.injective
  have hp : Function.Injective p :=
    fun s t h => ha.injective (Subtype.ext h)
  have hp₁ : Function.Injective p₁ := hr₁.injective
  have hranges : Set.range p₀.symm=Set.range r₀ := Path.symm_range p₀
  have hfirst : Set.range p₀.symm∩Set.range p={(a 0).val} := by
    rw [hranges]
    exact htrace₀
  have hfirstinj := actual_simple_path_concat p₀.symm p
    (hp₀.comp unitInterval.symm_involutive.injective) hp hfirst
  have hlast : Set.range (p₀.symm.trans p)∩Set.range p₁={(a 1).val} := by
    rw [Path.trans_range,Set.union_inter_distrib_right,hranges]
    have he : Set.range r₀∩Set.range r₁=∅ := Set.disjoint_iff_inter_eq_empty.mp hd
    have hpint : Set.range p∩Set.range p₁={(a 1).val} := by
      rw [Set.inter_comm]
      exact htrace₁
    have he' : Set.range r₀∩Set.range p₁=∅ := he
    rw [he',hpint,Set.empty_union]
  let P := (p₀.symm.trans p).trans p₁
  have hPi := actual_simple_path_concat (p₀.symm.trans p) p₁ hfirstinj hp₁ hlast
  let r : C(Interval,S) := ⟨P.toFun,P.continuous⟩
  have hrrange : Set.range r=(Set.range r₀∪Set.range (fun t => (a t).val))∪Set.range r₁ := by
    change Set.range P=_
    rw [Path.trans_range,Path.trans_range,hranges]
    rfl
  have hrclear : ∀ t,r t∉G := by
    intro t hg
    have hm := hrrange ▸ (Set.mem_range_self t : r t∈Set.range r)
    rcases hm with (⟨u,hu⟩ | ⟨u,hu⟩) | ⟨u,hu⟩
    · rw [←hu] at hg
      by_cases hu0 : u=0
      · exact hclear 0 (by simpa only [hu0,hzero₀] using hg)
      · exact hout u (bot_lt_iff_ne_bot.mpr hu0) (hF.frontier_subset (hG hg))
    · change (a u).val=r t at hu
      rw [←hu] at hg
      exact hclear u hg
    · rw [←hu] at hg
      exact Set.disjoint_left.mp disjoint_interior_frontier (hin u) (hG hg)
  obtain ⟨htail,hmid⟩ := actual_three_piece_connector_exact_affine_tail_clocks p₀.symm p p₁
  refine ⟨r,(r.continuous.isClosedEmbedding hPi).isEmbedding,
    P.source,P.target,?_,hrclear,hrrange,htail,hmid,
      actual_three_piece_connector_exact_affine_initial_clock p₀.symm p p₁⟩
  exact (P.source.symm ▸ hout 1 (by norm_num))

private theorem actual_embedded_outside_track_regional_first_curve_segment_retains_cap_clocks
    {X : Type} [TopologicalSpace X] [T2Space X]
    (F B G C : Set X) (hF : IsClosed F) (hC : IsClosed C)
    (hCi : C⊆interior F) (hfront : frontier F⊆B∪G)
    (q : C(Interval,X)) (hq : Topology.IsEmbedding q)
    (hq0 : q 0∉F) (hclear : ∀ t,q t∉G)
    (hmeet : ∃ t,q t∈C) :
    ∃ (p : C(Interval,↥F)) (clock : C(Interval,Interval)),
      Topology.IsEmbedding p ∧ Topology.IsEmbedding clock ∧
      (∀ t,(p t).val=q (clock t)) ∧
      (p 0).val∈B ∧
      (∀ t : Interval,0<t → (p t).val∈interior F) ∧
      (∀ t,(p t).val∈C ↔ t=1) ∧
      Set.range (fun t => (p t).val)⊆Set.range q ∧
      (∀ t,(clock t:ℝ)=(1-(t:ℝ))*(clock 0:ℝ)+(t:ℝ)*(clock 1:ℝ)) ∧
      q (clock 0)∉interior F := by
  let T : Set Interval := q ⁻¹' C
  have hT : IsCompact T := (hC.preimage q.continuous).isCompact
  obtain ⟨τ,hτ,hmin⟩ := hT.exists_isLeast hmeet
  have hτi : q τ∈interior F := hCi hτ
  let Z : Set Interval := Set.Icc 0 τ ∩ q ⁻¹' (interior F)ᶜ
  have hZ : IsCompact Z :=
    (isClosed_Icc.inter (isOpen_interior.isClosed_compl.preimage q.continuous)).isCompact
  have hZne : Z.Nonempty := ⟨0,⟨⟨le_rfl,bot_le⟩,fun hi => hq0 (interior_subset hi)⟩⟩
  obtain ⟨σ,hσ,hmax⟩ := hZ.exists_isGreatest hZne
  have hστ : σ<τ := lt_of_le_of_ne hσ.1.2 (fun he => hσ.2 (he.symm ▸ hτi))
  let clock : C(Interval,Interval) := {
    toFun := fun t => ⟨(σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ),by
      constructor <;> nlinarith [σ.property.1,σ.property.2,τ.property.1,
        τ.property.2,t.property.1,t.property.2,(show (σ:ℝ)<(τ:ℝ) from hστ)]⟩
    continuous_toFun := by fun_prop }
  have hc0 : clock 0=σ := Subtype.ext (by change (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*0=(σ:ℝ);ring)
  have hc1 : clock 1=τ := Subtype.ext (by change (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*1=(τ:ℝ);ring)
  have hclockinj : Function.Injective clock := by
    intro t u he
    have hev := congrArg Subtype.val he
    have hp : 0<(τ:ℝ)-(σ:ℝ) := sub_pos.mpr hστ
    apply Subtype.ext
    change (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ)=
      (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(u:ℝ) at hev
    nlinarith
  let r : C(Interval,X) := q.comp clock
  have hrI (t : Interval) (ht : 0<t) : r t∈interior F := by
    by_contra hn
    have hσc : σ<clock t := by
      change (σ:ℝ)<(σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ)
      have hp : 0<(τ:ℝ)-(σ:ℝ) := sub_pos.mpr hστ
      have htR : 0<(t:ℝ) := ht
      nlinarith
    have hcτ : clock t≤τ := by
      change (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ)≤(τ:ℝ)
      nlinarith [t.property.2,(show (σ:ℝ)<(τ:ℝ) from hστ)]
    have hcZ : clock t∈Z := ⟨⟨bot_le,hcτ⟩,hn⟩
    exact (not_le_of_gt hσc) (hmax hcZ)
  have h0cl : (0 : Interval)∈closure (Set.Ioo (0 : Interval) 1) := by
    rw [closure_Ioo (by norm_num : (0 : Interval)≠1)]
    exact ⟨le_rfl,bot_le⟩
  have hr0F : r 0∈F := by
    have hr0cl : r 0∈closure (r '' Set.Ioo (0 : Interval) 1) :=
      mem_closure_image r.continuous.continuousAt h0cl
    apply closure_minimal (s := r '' Set.Ioo (0 : Interval) 1) (t := F) _ hF hr0cl
    rintro y ⟨t,ht,rfl⟩
    exact interior_subset (hrI t ht.1)
  have hrF (t : Interval) : r t∈F := by
    by_cases ht : t=0
    · simpa only [ht] using hr0F
    · exact interior_subset (hrI t (bot_lt_iff_ne_bot.mpr ht))
  let p : C(Interval,↥F) := ⟨fun t => ⟨r t,hrF t⟩,r.continuous.subtype_mk _⟩
  have hp : Topology.IsEmbedding p := (hq.comp
    (clock.continuous.isClosedEmbedding hclockinj).isEmbedding).codRestrict _ hrF
  have hr0front : r 0∈frontier F := by
    apply (mem_frontier_iff_notMem_interior hr0F).mpr
    change q (clock 0)∉interior F
    rw [hc0]
    exact hσ.2
  have hr0B : r 0∈B := (hfront hr0front).resolve_right (hclear (clock 0))
  refine ⟨p,clock,hp,(clock.continuous.isClosedEmbedding hclockinj).isEmbedding,
    fun _ => rfl,hr0B,hrI,?_,?_,?_,?_⟩
  · intro t
    constructor
    · intro htC
      have htmin : τ≤clock t := hmin htC
      apply Subtype.ext
      change (t:ℝ)=1
      change (τ:ℝ)≤(σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ) at htmin
      nlinarith [t.property.2,(show (σ:ℝ)<(τ:ℝ) from hστ)]
    · intro ht
      subst t
      change q (clock 1)∈C
      rw [hc1]
      exact hτ
  · rintro y ⟨t,rfl⟩
    exact ⟨clock t,rfl⟩

  · intro t
    rw [hc0,hc1]
    change (σ:ℝ)+((τ:ℝ)-(σ:ℝ))*(t:ℝ)=
      (1-(t:ℝ))*(σ:ℝ)+(t:ℝ)*(τ:ℝ)
    ring
  · rw [hc0]
    exact hσ.2

private theorem actual_regional_first_curve_clock_cap_bounds_from_clearance
    {S : Type} [TopologicalSpace S]
    (F C : Set S) (q : C(Interval,S)) (clock : C(Interval,Interval))
    (hfirst : q (clock 1)∈C) (hboundary : q (clock 0)∉interior F)
    (b c : ℝ)
    (hlate : ∀ t : Interval,b≤(t:ℝ) → q t∈interior F)
    (hearly : ∀ t : Interval,(t:ℝ)≤c → q t∉C) :
    (clock 0:ℝ)<b ∧ c<(clock 1:ℝ) := by
  constructor
  · by_contra hn
    exact hboundary (hlate (clock 0) (le_of_not_gt hn))
  · by_contra hn
    exact hearly (clock 1) (le_of_not_gt hn) hfirst

private theorem actual_two_regional_rail_clocks_construct_ambient_rectangle_with_caps
    {S : Type} [TopologicalSpace S]
    (F U₀ U₁ : Set S)
    (E : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S))
    (p₀ p₁ : C(Interval,↥F)) (clock₀ clock₁ : C(Interval,Interval))
    (w₀ w₁ : ↥(Set.Icc (-1 : ℝ) 1)) (hw : (w₀:ℝ)≤(w₁:ℝ))
    (hrail₀ : ∀ t,(p₀ t).val=E (clock₀ t,w₀))
    (hrail₁ : ∀ t,(p₁ t).val=E (clock₁ t,w₁))
    (b c : ℝ) (hb₀ : (clock₀ 0:ℝ)≤b) (hb₁ : (clock₁ 0:ℝ)≤b)
    (hc₀ : c≤(clock₀ 1:ℝ)) (hc₁ : c≤(clock₁ 1:ℝ))
    (hcap₀ : ∀ t : Interval,(t:ℝ)≤b →
      ∀ w : ↥(Set.Icc (-1 : ℝ) 1),(w₀:ℝ)≤(w:ℝ) → (w:ℝ)≤(w₁:ℝ) → E (t,w)∈U₀)
    (hcap₁ : ∀ t : Interval,c≤(t:ℝ) →
      ∀ w : ↥(Set.Icc (-1 : ℝ) 1),(w₀:ℝ)≤(w:ℝ) → (w:ℝ)≤(w₁:ℝ) → E (t,w)∈U₁) :
    ∃ A : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S),
      (∀ t,A (t,⟨-1,by norm_num⟩)=(p₀ t).val) ∧
      (∀ t,A (t,⟨1,by norm_num⟩)=(p₁ t).val) ∧
      (∀ w,A (0,w)∈U₀) ∧ (∀ w,A (1,w)∈U₁) := by
  let blend : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),ℝ) :=
    ⟨fun z => ((z.2:ℝ)+1)/2,by fun_prop⟩
  have hblend (z : Interval × ↥(Set.Icc (-1 : ℝ) 1)) : 0≤blend z ∧ blend z≤1 := by
    dsimp [blend]
    constructor <;> linarith [z.2.property.1,z.2.property.2]
  let T : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),Interval) := {
    toFun := fun z => ⟨(1-blend z)*(clock₀ z.1:ℝ)+blend z*(clock₁ z.1:ℝ),
      (convex_Icc (0:ℝ) 1) (clock₀ z.1).property (clock₁ z.1).property
        (sub_nonneg.mpr (hblend z).2) (hblend z).1 (by ring)⟩
    continuous_toFun := by fun_prop }
  let W : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),↥(Set.Icc (-1 : ℝ) 1)) := {
    toFun := fun z => ⟨(1-blend z)*(w₀:ℝ)+blend z*(w₁:ℝ),
      (convex_Icc (-1:ℝ) 1) w₀.property w₁.property
        (sub_nonneg.mpr (hblend z).2) (hblend z).1 (by ring)⟩
    continuous_toFun := by fun_prop }
  have hW (z : Interval × ↥(Set.Icc (-1 : ℝ) 1)) :
      (w₀:ℝ)≤(W z:ℝ) ∧ (W z:ℝ)≤(w₁:ℝ) :=
    (convex_Icc (w₀:ℝ) (w₁:ℝ)) (show (w₀:ℝ)∈Set.Icc (w₀:ℝ) (w₁:ℝ) from ⟨le_rfl,hw⟩)
      (show (w₁:ℝ)∈Set.Icc (w₀:ℝ) (w₁:ℝ) from ⟨hw,le_rfl⟩)
      (sub_nonneg.mpr (hblend z).2) (hblend z).1 (by ring)
  let A : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S) :=
    ⟨fun z => E (T z,W z),by fun_prop⟩
  have hleftT (t : Interval) : T (t,⟨-1,by norm_num⟩)=clock₀ t := by
    apply Subtype.ext
    dsimp [T,blend]
    ring
  have hleftW (t : Interval) : W (t,⟨-1,by norm_num⟩)=w₀ := by
    apply Subtype.ext
    dsimp [W,blend]
    ring
  have hrightT (t : Interval) : T (t,⟨1,by norm_num⟩)=clock₁ t := by
    apply Subtype.ext
    dsimp [T,blend]
    ring
  have hrightW (t : Interval) : W (t,⟨1,by norm_num⟩)=w₁ := by
    apply Subtype.ext
    dsimp [W,blend]
    ring
  refine ⟨A,?_,?_,?_,?_⟩
  · intro t
    change E (T (t,⟨-1,by norm_num⟩),W (t,⟨-1,by norm_num⟩))=(p₀ t).val
    rw [hleftT,hleftW]
    exact (hrail₀ t).symm
  · intro t
    change E (T (t,⟨1,by norm_num⟩),W (t,⟨1,by norm_num⟩))=(p₁ t).val
    rw [hrightT,hrightW]
    exact (hrail₁ t).symm
  · intro w
    apply hcap₀ (T (0,w)) _ (W (0,w)) (hW (0,w)).1 (hW (0,w)).2
    change (1-blend (0,w))*(clock₀ 0:ℝ)+blend (0,w)*(clock₁ 0:ℝ)≤b
    have hweights := hblend (0,w)
    have h₀ := mul_nonneg (sub_nonneg.mpr hweights.2) (sub_nonneg.mpr hb₀)
    have h₁ := mul_nonneg hweights.1 (sub_nonneg.mpr hb₁)
    nlinarith
  · intro w
    apply hcap₁ (T (1,w)) _ (W (1,w)) (hW (1,w)).1 (hW (1,w)).2
    change c≤(1-blend (1,w))*(clock₀ 1:ℝ)+blend (1,w)*(clock₁ 1:ℝ)
    have hweights := hblend (1,w)
    have h₀ := mul_nonneg (sub_nonneg.mpr hweights.2) (sub_nonneg.mpr hc₀)
    have h₁ := mul_nonneg hweights.1 (sub_nonneg.mpr hc₁)
    nlinarith

private theorem actual_chart_crossing_strip_constructs_regional_rails_and_ambient_caps
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B G C U₀ U₁ : Set S) (hF : IsClosed F) (hC : IsClosed C)
    (hCi : C⊆interior F) (hfront : frontier F⊆B∪G)
    (E : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S))
    (hE : Topology.IsEmbedding E) (hclear : ∀ z,E z∉G)
    (N : OpenPartialHomeomorph S Schoenflies.Plane)
    (U : Set S) (hU : IsOpen U) (hUN : U⊆N.source)
    (θ b c : Interval)
    (hstart : E (0,⟨0,by norm_num⟩)∉F)
    (htail : ∀ t∈Set.Icc θ 1,E (t,⟨0,by norm_num⟩)∈U)
    (hpositive : 0<N (E (θ,⟨0,by norm_num⟩)) 0)
    (hnegative : N (E (1,⟨0,by norm_num⟩)) 0<0)
    (haxis : ∀ y∈U,N y 0=0 → y∈C)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hcenterF : ∀ t∈Set.Icc b 1,E (t,⟨0,by norm_num⟩)∈interior F)
    (hcenterC : ∀ t∈Set.Icc 0 c,E (t,⟨0,by norm_num⟩)∉C)
    (hcenter₀ : ∀ t∈Set.Icc 0 b,E (t,⟨0,by norm_num⟩)∈U₀)
    (hcenter₁ : ∀ t∈Set.Icc c 1,E (t,⟨0,by norm_num⟩)∈U₁) :
    ∃ (p₀ p₁ : C(Interval,↥F)) (A : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S)),
      Topology.IsEmbedding p₀ ∧ Topology.IsEmbedding p₁ ∧
      (p₀ 0).val∈B ∧ (p₁ 0).val∈B ∧
      (∀ t : Interval,0<t → (p₀ t).val∈interior F) ∧
      (∀ t : Interval,0<t → (p₁ t).val∈interior F) ∧
      (∀ t,(p₀ t).val∈C ↔ t=1) ∧
      (∀ t,(p₁ t).val∈C ↔ t=1) ∧
      Disjoint (Set.range (fun t => (p₀ t).val)) (Set.range (fun t => (p₁ t).val)) ∧
      (∀ t,A (t,⟨-1,by norm_num⟩)=(p₀ t).val) ∧
      (∀ t,A (t,⟨1,by norm_num⟩)=(p₁ t).val) ∧
      (∀ w,A (0,w)∈U₀) ∧ (∀ w,A (1,w)∈U₁) := by
  obtain ⟨δS,hδS,_,hwidth⟩ := actual_small_strip_widths_cross_terminal_chart_axis
    F C hF E N U hU hUN θ hstart htail hpositive hnegative haxis
  obtain ⟨δF,hδF,_,hwholeF⟩ := actual_strip_compact_center_interval_uniform_clearance
    E (Set.Icc b 1) isCompact_Icc (interior F) isOpen_interior hcenterF
  obtain ⟨δC,hδC,_,hwholeC⟩ := actual_strip_compact_center_interval_uniform_clearance
    E (Set.Icc 0 c) isCompact_Icc Cᶜ hC.isOpen_compl hcenterC
  obtain ⟨δ₀,hδ₀,_,hwhole₀⟩ := actual_strip_compact_center_interval_uniform_clearance
    E (Set.Icc 0 b) isCompact_Icc U₀ hU₀ hcenter₀
  obtain ⟨δ₁,hδ₁,hδ₁one,hwhole₁⟩ := actual_strip_compact_center_interval_uniform_clearance
    E (Set.Icc c 1) isCompact_Icc U₁ hU₁ hcenter₁
  let δ := min δS (min δF (min δC (min δ₀ δ₁)))
  have hδ : 0<δ := lt_min hδS (lt_min hδF (lt_min hδC (lt_min hδ₀ hδ₁)))
  have hδS' : δ≤δS := min_le_left _ _
  have hδF' : δ≤δF := (min_le_right _ _).trans (min_le_left _ _)
  have hδC' : δ≤δC := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδ₀' : δ≤δ₀ := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hδ₁' : δ≤δ₁ := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have hδone : δ<1 := hδ₁'.trans_lt hδ₁one
  let w₀ : ↥(Set.Icc (-1 : ℝ) 1) := ⟨-δ/2,by constructor <;> linarith⟩
  let w₁ : ↥(Set.Icc (-1 : ℝ) 1) := ⟨δ/2,by constructor <;> linarith⟩
  have hw₀ : |(w₀:ℝ)|≤δ := by change |-δ/2|≤δ;rw [abs_of_neg (by linarith)];linarith
  have hw₁ : |(w₁:ℝ)|≤δ := by change |δ/2|≤δ;rw [abs_of_pos (by linarith)];linarith
  have hwne : w₀≠w₁ := by
    intro he
    have hev := congrArg Subtype.val he
    change -δ/2=δ/2 at hev
    linarith
  have hwle : (w₀:ℝ)≤(w₁:ℝ) := by change -δ/2≤δ/2;linarith
  let q₀ : C(Interval,S) := ⟨fun t => E (t,w₀),by fun_prop⟩
  let q₁ : C(Interval,S) := ⟨fun t => E (t,w₁),by fun_prop⟩
  have hq₀ : Topology.IsEmbedding q₀ :=
    (q₀.continuous.isClosedEmbedding (fun s t h => congrArg Prod.fst (hE.injective h))).isEmbedding
  have hq₁ : Topology.IsEmbedding q₁ :=
    (q₁.continuous.isClosedEmbedding (fun s t h => congrArg Prod.fst (hE.injective h))).isEmbedding
  obtain ⟨p₀,clock₀,hp₀,_,htrace₀,hB₀,hI₀,hPC₀,hrange₀,_,hoff₀⟩ :=
    actual_embedded_outside_track_regional_first_curve_segment_retains_cap_clocks
      F B G C hF hC hCi hfront q₀ hq₀ (hwidth w₀ (hw₀.trans hδS')).1
      (fun t => hclear (t,w₀)) (hwidth w₀ (hw₀.trans hδS')).2
  obtain ⟨p₁,clock₁,hp₁,_,htrace₁,hB₁,hI₁,hPC₁,hrange₁,_,hoff₁⟩ :=
    actual_embedded_outside_track_regional_first_curve_segment_retains_cap_clocks
      F B G C hF hC hCi hfront q₁ hq₁ (hwidth w₁ (hw₁.trans hδS')).1
      (fun t => hclear (t,w₁)) (hwidth w₁ (hw₁.trans hδS')).2
  have hlast₀ : q₀ (clock₀ 1)∈C := by rw [←htrace₀];exact (hPC₀ 1).mpr rfl
  have hlast₁ : q₁ (clock₁ 1)∈C := by rw [←htrace₁];exact (hPC₁ 1).mpr rfl
  obtain ⟨hb₀,hc₀⟩ := actual_regional_first_curve_clock_cap_bounds_from_clearance
    F C q₀ clock₀ hlast₀ hoff₀ b c
    (fun t ht => hwholeF t ⟨ht,le_top⟩ w₀ (hw₀.trans hδF'))
    (fun t ht => hwholeC t ⟨bot_le,ht⟩ w₀ (hw₀.trans hδC'))
  obtain ⟨hb₁,hc₁⟩ := actual_regional_first_curve_clock_cap_bounds_from_clearance
    F C q₁ clock₁ hlast₁ hoff₁ b c
    (fun t ht => hwholeF t ⟨ht,le_top⟩ w₁ (hw₁.trans hδF'))
    (fun t ht => hwholeC t ⟨bot_le,ht⟩ w₁ (hw₁.trans hδC'))
  have habsw (w : ↥(Set.Icc (-1 : ℝ) 1)) (hl : (w₀:ℝ)≤(w:ℝ))
      (hu : (w:ℝ)≤(w₁:ℝ)) : |(w:ℝ)|≤δ := by
    apply abs_le.mpr
    change -δ/2≤(w:ℝ) at hl
    change (w:ℝ)≤δ/2 at hu
    constructor <;> linarith
  obtain ⟨A,hleft,hright,hcap₀,hcap₁⟩ :=
    actual_two_regional_rail_clocks_construct_ambient_rectangle_with_caps
      F U₀ U₁ E p₀ p₁ clock₀ clock₁ w₀ w₁ hwle htrace₀ htrace₁ b c hb₀.le hb₁.le hc₀.le hc₁.le
      (fun t ht w hl hu => hwhole₀ t ⟨bot_le,ht⟩ w ((habsw w hl hu).trans hδ₀'))
      (fun t ht w hl hu => hwhole₁ t ⟨ht,le_top⟩ w ((habsw w hl hu).trans hδ₁'))
  have hdq : Disjoint (Set.range q₀) (Set.range q₁) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨s,hs⟩ ⟨t,ht⟩
    exact hwne (congrArg Prod.snd (hE.injective (hs.trans ht.symm)))
  exact ⟨p₀,p₁,A,hp₀,hp₁,hB₀,hB₁,hI₀,hI₁,hPC₀,hPC₁,
    hdq.mono hrange₀ hrange₁,hleft,hright,hcap₀,hcap₁⟩

private theorem actual_continuous_arc_initial_open_patch_closed_prefix
    {X : Type} [TopologicalSpace X]
    (a : C(Interval,X)) (U : Set X) (hU : IsOpen U) (ha0 : a 0∈U) :
    ∃ α : Interval,0<(α:ℝ) ∧ (α:ℝ)<1 ∧
      ∀ t∈Set.Icc 0 α,a t∈U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (hU.preimage a.continuous) 0 ha0
  let δ := min ε 1 / 2
  have hδ : 0<δ := half_pos (lt_min hε (by norm_num))
  have hδε : δ<ε := (half_lt_self (lt_min hε (by norm_num))).trans_le (min_le_left _ _)
  have hδhalf : δ≤1/2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let α : Interval := ⟨δ,by constructor <;> linarith⟩
  refine ⟨α,hδ,hδhalf.trans_lt (by norm_num),?_⟩
  intro t ht
  apply hball
  change dist t (0 : Interval)<ε
  rw [Subtype.dist_eq,Real.dist_eq]
  change |(t:ℝ)-0|<ε
  rw [sub_zero,abs_of_nonneg t.property.1]
  have htR : (t:ℝ)≤δ := ht.2
  exact htR.trans_lt hδε

private theorem actual_three_piece_connector_produces_cap_center_intervals
    {X : Type} [TopologicalSpace X]
    {x y z w : X} (p₀ : Path x y) (p : Path y z) (p₁ : Path z w)
    (F C U₀ U₁ : Set X)
    (α₀ α₁ : Interval) (hα₀ : 0<(α₀:ℝ)) (hα₀one : (α₀:ℝ)<1)
    (hα₁ : 0<(α₁:ℝ)) (hα₁one : (α₁:ℝ)<1)
    (hfirst : ∀ t,p₀ t∈U₀)
    (hprefix : ∀ t∈Set.Icc 0 α₀,p t∈U₀)
    (hmidinside : ∀ t : Interval,0<t → p t∈interior F)
    (hlastinside : ∀ t,p₁ t∈interior F)
    (htail : ∀ t∈Set.Icc α₁ 1,p t∈U₁)
    (hlast : ∀ t,p₁ t∈U₁)
    (hcircle : ∀ t,((p₀.trans p).trans p₁) t∈C ↔
      t=⟨1/2,by norm_num⟩) :
    ∃ b c : Interval,0<(b:ℝ) ∧ (b:ℝ)<1 ∧
      0<(c:ℝ) ∧ (c:ℝ)<1/2 ∧
      (∀ t∈Set.Icc 0 b,((p₀.trans p).trans p₁) t∈U₀) ∧
      (∀ t∈Set.Icc b 1,((p₀.trans p).trans p₁) t∈interior F) ∧
      (∀ t∈Set.Icc 0 c,((p₀.trans p).trans p₁) t∉C) ∧
      (∀ t∈Set.Icc c 1,((p₀.trans p).trans p₁) t∈U₁) ∧
      ((p₀.trans p).trans p₁) c=p α₁ := by
  let b : Interval := ⟨(1+(α₀:ℝ))/4,by constructor <;> linarith⟩
  let c : Interval := ⟨(1+(α₁:ℝ))/4,by constructor <;> linarith⟩
  have hb : (b:ℝ)=(1+(α₀:ℝ))/4 := rfl
  have hc : (c:ℝ)=(1+(α₁:ℝ))/4 := rfl
  obtain ⟨hfinal,hmid⟩ := actual_three_piece_connector_exact_affine_tail_clocks p₀ p p₁
  obtain ⟨hterminal,hcontact,_⟩ :=
    actual_three_piece_connector_terminal_chart_control p₀ p p₁ c α₁
      (by rw [hc];linarith) (by rw [hc];linarith)
      (by rw [hc];ring) U₁ htail hlast
  refine ⟨b,c,by rw [hb];linarith,by rw [hb];linarith,
    by rw [hc];linarith,by rw [hc];linarith,?_,?_,?_,hterminal,hcontact⟩
  · intro t ht
    have htb : (t:ℝ)≤(b:ℝ) := ht.2
    by_cases htquarter : (t:ℝ)≤1/4
    · rw [actual_three_piece_connector_exact_affine_initial_clock p₀ p p₁ t htquarter]
      let u : Interval := ⟨4*(t:ℝ),by constructor <;> linarith [t.property.1]⟩
      exact (Path.extend_apply p₀ u.property).symm ▸ hfirst u
    · rw [hmid t (by linarith) (by rw [hb] at htb;linarith)]
      let u : Interval := ⟨4*(t:ℝ)-1,by constructor <;> rw [hb] at htb <;> linarith⟩
      have hu : u∈Set.Icc 0 α₀ := by
        constructor
        · exact u.property.1
        · change 4*(t:ℝ)-1≤(α₀:ℝ)
          rw [hb] at htb
          linarith
      exact (Path.extend_apply p u.property).symm ▸ hprefix u hu
  · intro t ht
    have hbt : (b:ℝ)≤(t:ℝ) := ht.1
    by_cases hhalf : (t:ℝ)≤1/2
    · rw [hmid t (by rw [hb] at hbt;linarith) hhalf]
      let u : Interval := ⟨4*(t:ℝ)-1,by constructor <;> rw [hb] at hbt <;> linarith⟩
      have hu : 0<u := by change 0<4*(t:ℝ)-1;rw [hb] at hbt;linarith
      exact (Path.extend_apply p u.property).symm ▸ hmidinside u hu
    · rw [hfinal t (le_of_lt (not_le.mp hhalf))]
      let u : Interval := ⟨2*(t:ℝ)-1,by constructor <;> linarith [t.property.2]⟩
      exact (Path.extend_apply p₁ u.property).symm ▸ hlastinside u
  · intro t ht htC
    have heq := (hcircle t).mp htC
    have htc : (t:ℝ)≤(c:ℝ) := ht.2
    have htval := congrArg Subtype.val heq
    change (t:ℝ)=1/2 at htval
    rw [hc] at htc
    linarith

private theorem actual_three_affine_clock_connector_equals_concatenation
    {X : Type} [TopologicalSpace X]
    {x y z w : X} (p₀ : Path x y) (p : Path y z) (p₁ : Path z w)
    (r : C(Interval,X))
    (hfirst : ∀ t : Interval,(t:ℝ)≤1/4 → r t=p₀.extend (4*(t:ℝ)))
    (hmid : ∀ t : Interval,1/4≤(t:ℝ) → (t:ℝ)≤1/2 →
      r t=p.extend (4*(t:ℝ)-1))
    (hlast : ∀ t : Interval,1/2≤(t:ℝ) → r t=p₁.extend (2*(t:ℝ)-1)) :
    ∀ t,r t=((p₀.trans p).trans p₁) t := by
  obtain ⟨htail,hcenter⟩ := actual_three_piece_connector_exact_affine_tail_clocks p₀ p p₁
  intro t
  by_cases hquarter : (t:ℝ)≤1/4
  · rw [hfirst t hquarter,
      actual_three_piece_connector_exact_affine_initial_clock p₀ p p₁ t hquarter]
  · by_cases hhalf : (t:ℝ)≤1/2
    · rw [hmid t (le_of_lt (not_le.mp hquarter)) hhalf,
        hcenter t (le_of_lt (not_le.mp hquarter)) hhalf]
    · rw [hlast t (le_of_lt (not_le.mp hhalf)),htail t (le_of_lt (not_le.mp hhalf))]

private theorem actual_three_affine_clock_connector_produces_actual_cap_intervals
    {X : Type} [TopologicalSpace X]
    {x y z w : X} (p₀ : Path x y) (p : Path y z) (p₁ : Path z w)
    (r : C(Interval,X)) (F C U₀ U₁ : Set X)
    (hclock₀ : ∀ t : Interval,(t:ℝ)≤1/4 → r t=p₀.extend (4*(t:ℝ)))
    (hclockmid : ∀ t : Interval,1/4≤(t:ℝ) → (t:ℝ)≤1/2 →
      r t=p.extend (4*(t:ℝ)-1))
    (hclock₁ : ∀ t : Interval,1/2≤(t:ℝ) → r t=p₁.extend (2*(t:ℝ)-1))
    (α₀ α₁ : Interval) (hα₀ : 0<(α₀:ℝ)) (hα₀one : (α₀:ℝ)<1)
    (hα₁ : 0<(α₁:ℝ)) (hα₁one : (α₁:ℝ)<1)
    (hfirst : ∀ t,p₀ t∈U₀)
    (hprefix : ∀ t∈Set.Icc 0 α₀,p t∈U₀)
    (hmidinside : ∀ t : Interval,0<t → p t∈interior F)
    (hlastinside : ∀ t,p₁ t∈interior F)
    (htail : ∀ t∈Set.Icc α₁ 1,p t∈U₁)
    (hlast : ∀ t,p₁ t∈U₁)
    (hcircle : ∀ t,r t∈C ↔ t=⟨1/2,by norm_num⟩) :
    ∃ b c : Interval,0<(b:ℝ) ∧ (b:ℝ)<1 ∧
      0<(c:ℝ) ∧ (c:ℝ)<1/2 ∧
      (∀ t∈Set.Icc 0 b,r t∈U₀) ∧
      (∀ t∈Set.Icc b 1,r t∈interior F) ∧
      (∀ t∈Set.Icc 0 c,r t∉C) ∧
      (∀ t∈Set.Icc c 1,r t∈U₁) ∧ r c=p α₁ := by
  have heq := actual_three_affine_clock_connector_equals_concatenation p₀ p p₁ r
    hclock₀ hclockmid hclock₁
  have hcircle' : ∀ t,((p₀.trans p).trans p₁) t∈C ↔
      t=⟨1/2,by norm_num⟩ := by
    intro t
    rw [←heq t]
    exact hcircle t
  obtain ⟨b,c,hb,hbone,hc,hchalf,hbase,hinside,hclear,hterminal,hcontact⟩ :=
    actual_three_piece_connector_produces_cap_center_intervals p₀ p p₁ F C U₀ U₁
      α₀ α₁ hα₀ hα₀one hα₁ hα₁one hfirst hprefix hmidinside hlastinside htail hlast hcircle'
  refine ⟨b,c,hb,hbone,hc,hchalf,?_,?_,?_,?_,?_⟩
  · intro t ht
    rw [heq t]
    exact hbase t ht
  · intro t ht
    rw [heq t]
    exact hinside t ht
  · intro t ht
    rw [heq t]
    exact hclear t ht
  · intro t ht
    rw [heq t]
    exact hterminal t ht
  · rw [heq c]
    exact hcontact

private theorem actual_three_clock_extended_connector_constructs_regional_rails_with_caps
    {S : Type} [TopologicalSpace S] [T2Space S]
    {x y z w : S} (p₀ : Path x y) (p : Path y z) (p₁ : Path z w)
    (r : C(Interval,S)) (F B G C U₀ U₁ : Set S)
    (hF : IsClosed F) (hC : IsClosed C) (hCi : C⊆interior F)
    (hfront : frontier F⊆B∪G)
    (hclock₀ : ∀ t : Interval,(t:ℝ)≤1/4 → r t=p₀.extend (4*(t:ℝ)))
    (hclockmid : ∀ t : Interval,1/4≤(t:ℝ) → (t:ℝ)≤1/2 →
      r t=p.extend (4*(t:ℝ)-1))
    (hclock₁ : ∀ t : Interval,1/2≤(t:ℝ) → r t=p₁.extend (2*(t:ℝ)-1))
    (hU₀ : IsOpen U₀) (hpzero : p 0∈U₀)
    (hfirst : ∀ t,p₀ t∈U₀)
    (hmidinside : ∀ t : Interval,0<t → p t∈interior F)
    (hlastinside : ∀ t,p₁ t∈interior F)
    (N : OpenPartialHomeomorph S Schoenflies.Plane)
    (hU₁ : IsOpen U₁) (hU₁N : U₁⊆N.source)
    (α₁ : Interval) (hα₁ : 0<(α₁:ℝ)) (hα₁one : (α₁:ℝ)<1)
    (htail : ∀ t∈Set.Icc α₁ 1,p t∈U₁)
    (hlast : ∀ t,p₁ t∈U₁)
    (hpositive : 0<N (p α₁) 0) (hnegative : N (p₁ 1) 0<0)
    (haxis : ∀ y∈U₁,N y 0=0 → y∈C)
    (hcircle : ∀ t,r t∈C ↔ t=⟨1/2,by norm_num⟩)
    (E : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S))
    (hE : Topology.IsEmbedding E) (hclear : ∀ z,E z∉G)
    (hcenter : ∀ t,E (t,⟨0,by norm_num⟩)=r t) (hstart : r 0∉F) :
    ∃ (p₀ p₁ : C(Interval,↥F)) (A : C(Interval × ↥(Set.Icc (-1 : ℝ) 1),S)),
      Topology.IsEmbedding p₀ ∧ Topology.IsEmbedding p₁ ∧
      (p₀ 0).val∈B ∧ (p₁ 0).val∈B ∧
      (∀ t : Interval,0<t → (p₀ t).val∈interior F) ∧
      (∀ t : Interval,0<t → (p₁ t).val∈interior F) ∧
      (∀ t,(p₀ t).val∈C ↔ t=1) ∧
      (∀ t,(p₁ t).val∈C ↔ t=1) ∧
      Disjoint (Set.range (fun t => (p₀ t).val)) (Set.range (fun t => (p₁ t).val)) ∧
      (∀ t,A (t,⟨-1,by norm_num⟩)=(p₀ t).val) ∧
      (∀ t,A (t,⟨1,by norm_num⟩)=(p₁ t).val) ∧
      (∀ w,A (0,w)∈U₀) ∧ (∀ w,A (1,w)∈U₁) := by
  obtain ⟨α₀,hα₀,hα₀one,hprefix⟩ :=
    actual_continuous_arc_initial_open_patch_closed_prefix p.toContinuousMap U₀ hU₀ hpzero
  obtain ⟨b,c,_,_,_,_,hbase,hinside,hCclear,hterminal,hcontact⟩ :=
    actual_three_affine_clock_connector_produces_actual_cap_intervals p₀ p p₁ r F C U₀ U₁
      hclock₀ hclockmid hclock₁ α₀ α₁ hα₀ hα₀one hα₁ hα₁one hfirst hprefix
      hmidinside hlastinside htail hlast hcircle
  have hrone : r 1=p₁ 1 := by
    rw [hclock₁ 1 (by norm_num)]
    norm_num
  apply actual_chart_crossing_strip_constructs_regional_rails_and_ambient_caps
    F B G C U₀ U₁ hF hC hCi hfront E hE hclear N U₁ hU₁ hU₁N c b c
  · rw [hcenter]
    exact hstart
  · intro t ht
    rw [hcenter]
    exact hterminal t ht
  · rw [hcenter,hcontact]
    exact hpositive
  · rw [hcenter,hrone]
    exact hnegative
  · exact haxis
  · exact hU₀
  · exact hU₁
  · intro t ht
    rw [hcenter]
    exact hinside t ht
  · intro t ht
    rw [hcenter]
    exact hCclear t ht
  · intro t ht
    rw [hcenter]
    exact hbase t ht
  · intro t ht
    rw [hcenter]
    exact hterminal t ht

private theorem actual_axis_chart_square_shrinks_into_given_open_ambient_cap
    {S : Type} [TopologicalSpace S]
    (N : OpenPartialHomeomorph S Schoenflies.Plane)
    (p : S) (hp : p∈N.source) (hz : N p=0)
    (η : ℝ) (hη : 0<η)
    (U : Set S) (hU : IsOpen U) (hpU : p∈U) :
    ∃ ρ : ℝ,0<ρ ∧ ρ<η ∧
      Schoenflies.Plane.openSquare 0 ρ⊆N.target ∧
      N.symm '' Schoenflies.Plane.openSquare 0 ρ⊆U := by
  let W : Set Schoenflies.Plane := N.target∩N.symm ⁻¹' U
  have hW : IsOpen W := N.isOpen_inter_preimage_symm hU
  have h0W : (0:Schoenflies.Plane)∈W := by
    constructor
    · exact hz ▸ N.map_source hp
    · change N.symm 0∈U
      rw [←hz,N.left_inv hp]
      exact hpU
  obtain ⟨ρ,hρ,hρη,hρW⟩ := Schoenflies.Plane.exists_openSquare_subset hW h0W (half_pos hη)
  refine ⟨ρ,hρ,hρη.trans_lt (half_lt_self hη),fun z hz => (hρW hz).1,?_⟩
  rintro y ⟨z,hz,rfl⟩
  exact (hρW hz).2

private theorem actual_extended_regional_connector_unique_middle_circle_contact
    {S : Type} [TopologicalSpace S]
    (F C : Set S) (hCF : C⊆F) (a : C(Interval,↥F))
    (hcircle : ∀ t,(a t).val∈C ↔ t=1)
    (r₀ r₁ r : C(Interval,S)) (hr : Topology.IsEmbedding r)
    (hz₀ : r₀ 0=(a 0).val) (hz₁ : r₁ 0=(a 1).val)
    (hout : ∀ t : Interval,0<t → r₀ t∉F)
    (hoff : ∀ t : Interval,0<t → r₁ t∉C)
    (hrrange : Set.range r=(Set.range r₀∪Set.range (fun t => (a t).val))∪Set.range r₁)
    (hhalf : r ⟨1/2,by norm_num⟩=(a 1).val) :
    ∀ t,r t∈C ↔ t=⟨1/2,by norm_num⟩ := by
  intro t
  constructor
  · intro htC
    have hmem : r t∈(Set.range r₀∪Set.range (fun u => (a u).val))∪Set.range r₁ :=
      hrrange ▸ Set.mem_range_self t
    have he : r t=(a 1).val := by
      rcases hmem with (⟨u,hu⟩ | ⟨u,hu⟩) | ⟨u,hu⟩
      · have huC : r₀ u∈C := hu.symm ▸ htC
        by_cases hu0 : u=0
        · have ha0C : (a 0).val∈C := by simpa only [hu0,hz₀] using huC
          have he01 : (0:Interval)=1 := (hcircle 0).mp ha0C
          exact False.elim (zero_ne_one he01)
        · exact False.elim (hout u (bot_lt_iff_ne_bot.mpr hu0) (hCF huC))
      · have huC : (a u).val∈C := by
          change (a u).val=r t at hu
          exact hu.symm ▸ htC
        have hu1 : u=1 := (hcircle u).mp huC
        exact hu.symm.trans (congrArg (fun v => (a v).val) hu1)
      · have huC : r₁ u∈C := hu.symm ▸ htC
        have hu0 : u=0 := by
          by_contra hn
          exact hoff u (bot_lt_iff_ne_bot.mpr hn) huC
        exact hu.symm.trans ((congrArg r₁ hu0).trans hz₁)
    exact hr.injective (he.trans hhalf.symm)
  · rintro rfl
    rw [hhalf]
    exact (hcircle 1).mpr rfl

private theorem actual_terminal_chart_axis_distinct_endpoints_short_curve_arc
    {S : Type} [TopologicalSpace S] [T2Space S]
    (C : Set S) (N : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ)
    (htarget : Schoenflies.Plane.openSquare 0 η⊆N.target)
    (haxis : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,y∈C ↔ N y 0=0)
    (p q : S) (hp : p∈N.symm '' Schoenflies.Plane.openSquare 0 η)
    (hq : q∈N.symm '' Schoenflies.Plane.openSquare 0 η)
    (hpC : p∈C) (hqC : q∈C) (hne : p≠q) :
    ∃ k : C(Interval,S),Topology.IsEmbedding k ∧ k 0=p ∧ k 1=q ∧
      Set.range k⊆C ∧ Set.range k⊆N.symm '' Schoenflies.Plane.openSquare 0 η := by
  obtain ⟨v,hv,hvp⟩ := hp
  obtain ⟨w,hw,hwq⟩ := hq
  have hpN : p∈N.source := hvp ▸ N.map_target (htarget hv)
  have hqN : q∈N.source := hwq ▸ N.map_target (htarget hw)
  have hNp : N p=v := by rw [←hvp,N.right_inv (htarget hv)]
  have hNq : N q=w := by rw [←hwq,N.right_inv (htarget hw)]
  have hNpSq : N p∈Schoenflies.Plane.openSquare 0 η := hNp.symm ▸ hv
  have hNqSq : N q∈Schoenflies.Plane.openSquare 0 η := hNq.symm ▸ hw
  have hNne : N p≠N q := fun he => hne (N.injOn hpN hqN he)
  let line : Path (N p) (N q) := Path.segment (N p) (N q)
  have hline : ∀ t,line t∈Schoenflies.Plane.openSquare 0 η := by
    intro t
    apply (Schoenflies.Plane.convex_openSquare 0 η).segment_subset hNpSq hNqSq
    rw [←Path.range_segment]
    exact Set.mem_range_self t
  let k : C(Interval,S) := ⟨fun t => N.symm (line t),
    N.continuousOn_symm.comp_continuous line.continuous (fun t => htarget (hline t))⟩
  have hki : Function.Injective k := by
    intro t u he
    exact Path.segment_injective_of_ne hNne
      (N.symm.injOn (htarget (hline t)) (htarget (hline u)) he)
  have hkpatch : ∀ t,k t∈N.symm '' Schoenflies.Plane.openSquare 0 η :=
    fun t => ⟨line t,hline t,rfl⟩
  have hp0 : N p 0=0 := (haxis p ⟨v,hv,hvp⟩).mp hpC
  have hq0 : N q 0=0 := (haxis q ⟨w,hw,hwq⟩).mp hqC
  refine ⟨k,(k.continuous.isClosedEmbedding hki).isEmbedding,?_,?_,?_,?_⟩
  · change N.symm (line 0)=p
    rw [line.source,N.left_inv hpN]
  · change N.symm (line 1)=q
    rw [line.target,N.left_inv hqN]
  · rintro y ⟨t,rfl⟩
    apply (haxis _ (hkpatch t)).mpr
    change N (N.symm (line t)) 0=0
    rw [N.right_inv (htarget (hline t))]
    change (Path.segment (N p) (N q) t) 0=0
    simp [Path.segment_apply,AffineMap.lineMap_apply_module,hp0,hq0]
  · rintro y ⟨t,rfl⟩
    exact hkpatch t

private theorem actual_mixed_clean_connector_constructs_regional_rails_actual_caps_and_short_curve_arc
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Schoenflies.Plane S]
    (F B G C : Set S) (hF : IsClosed F) (hC : IsClosed C) (hGclosed : IsClosed G)
    (hCi : C⊆interior F) (hGfront : G⊆frontier F) (hfront : frontier F⊆B∪G)
    (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
    (hainside : ∀ t : Interval,0<t → (a t).val∈interior F)
    (ha0front : (a 0).val∈frontier F)
    (hclear : ∀ t,(a t).val∉G) (hcircle : ∀ t,(a t).val∈C ↔ t=1)
    (N₀ N₁ : OpenPartialHomeomorph S Schoenflies.Plane) (η₀ η₁ : ℝ)
    (hp₀ : (a 0).val∈N₀.source) (hz₀ : N₀ (a 0).val=0)
    (hη₀ : 0<η₀) (_ht₀ : Schoenflies.Plane.openSquare 0 η₀⊆N₀.target)
    (hl₀ : ∀ y∈N₀.symm '' Schoenflies.Plane.openSquare 0 η₀,y∈F ↔ 0≤N₀ y 0)
    (hp₁ : (a 1).val∈N₁.source) (hz₁ : N₁ (a 1).val=0)
    (hη₁ : 0<η₁) (_ht₁ : Schoenflies.Plane.openSquare 0 η₁⊆N₁.target)
    (hl₁ : ∀ y∈N₁.symm '' Schoenflies.Plane.openSquare 0 η₁,
      y∈interior F ∧
      (y∈Set.range (fun t => (a t).val) ↔ 0≤N₁ y 0 ∧ N₁ y 1=0) ∧
      (y∈C ↔ N₁ y 0=0))
    (U₀ U₁ : Set S) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (ha₀U : (a 0).val∈U₀) (ha₁U : (a 1).val∈U₁) :
    ∃ (P Q : C(Interval,↥F)) (M : C(Interval × Set.Icc (-1 : ℝ) 1,S))
      (k : C(Interval,S)),
      Topology.IsEmbedding P ∧ Topology.IsEmbedding Q ∧
      (P 0).val∈B ∧ (Q 0).val∈B ∧
      (∀ t : Interval,0<t → (P t).val∈interior F) ∧
      (∀ t : Interval,0<t → (Q t).val∈interior F) ∧
      (∀ t,(P t).val∈C ↔ t=1) ∧
      (∀ t,(Q t).val∈C ↔ t=1) ∧
      Disjoint (Set.range (fun t => (P t).val)) (Set.range (fun t => (Q t).val)) ∧
      (∀ t,M (t,⟨1,by norm_num⟩)=(P t).val) ∧
      (∀ t,M (t,⟨-1,by norm_num⟩)=(Q t).val) ∧
      (∀ w,M (0,w)∈U₀) ∧ (∀ w,M (1,w)∈U₁) ∧
      Topology.IsEmbedding k ∧ k 0=(P 1).val ∧ k 1=(Q 1).val ∧
      Set.range k⊆C ∧ Set.range k⊆U₁ := by
  obtain ⟨ρ₀,hρ₀,hρ₀η,htρ₀,hcap₀⟩ :=
    actual_axis_chart_square_shrinks_into_given_open_ambient_cap N₀ (a 0).val
      hp₀ hz₀ η₀ hη₀ U₀ hU₀ ha₀U
  obtain ⟨ρ₁,hρ₁,hρ₁η,htρ₁,hcap₁⟩ :=
    actual_axis_chart_square_shrinks_into_given_open_ambient_cap N₁ (a 1).val
      hp₁ hz₁ η₁ hη₁ U₁ hU₁ ha₁U
  have hsmall₀ : N₀.symm '' Schoenflies.Plane.openSquare 0 ρ₀⊆
      N₀.symm '' Schoenflies.Plane.openSquare 0 η₀ := by
    apply Set.image_mono
    intro v hv
    exact lt_trans hv hρ₀η
  have hsmall₁ : N₁.symm '' Schoenflies.Plane.openSquare 0 ρ₁⊆
      N₁.symm '' Schoenflies.Plane.openSquare 0 η₁ := by
    apply Set.image_mono
    intro v hv
    exact lt_trans hv hρ₁η
  obtain ⟨r₀,hr₀,hzR₀,hoR₀,htR₀,hpatchR₀⟩ :=
    actual_negative_chart_halfplane_ray_from_positive_square F a N₀ ρ₀ hp₀ hz₀ hρ₀ htρ₀
      (fun y hy => hl₀ y (hsmall₀ hy))
  obtain ⟨r₁,hr₁,hzR₁,hiR₁,hoffR₁,htR₁,hpatchR₁,hcoordR₁,_⟩ :=
    actual_negative_terminal_chart_ray_with_signed_coordinates F C a N₁ ρ₁ hp₁ hz₁ hρ₁ htρ₁
      (fun y hy => hl₁ y (hsmall₁ hy))
  have hd : Disjoint (Set.range r₀) (Set.range r₁) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t,ht⟩ ⟨u,hu⟩
    have hi : r₀ t∈interior F := ht ▸ hu.symm ▸ hiR₁ u
    by_cases ht0 : t=0
    · have h0i : (a 0).val∈interior F := by simpa only [ht0,hzR₀] using hi
      exact Set.disjoint_left.mp disjoint_interior_frontier h0i ha0front
    · exact hoR₀ t (bot_lt_iff_ne_bot.mpr ht0) (interior_subset hi)
  obtain ⟨r,hr,hr0,hr1,hrout,hrclear,hrrange,hrtail,hrmid,hrinitial⟩ :=
    actual_two_negative_rays_extend_regional_connector_with_three_exact_clocks
      F G hF hGfront a ha hclear r₀ r₁ hr₀ hr₁ hzR₀ hzR₁ hoR₀ hiR₁ htR₀ htR₁ hd
  obtain ⟨E,hE,hcenter,hEU⟩ := source_whole_embedded_arc_strip r hr Gᶜ hGclosed.isOpen_compl
    (by rintro y ⟨t,rfl⟩;exact hrclear t)
  let EE : C(Interval × Set.Icc (-1 : ℝ) 1,S) := ⟨E,hE.continuous⟩
  let U : Set S := N₁.symm '' Schoenflies.Plane.openSquare 0 ρ₁
  have hU : IsOpen U := N₁.symm.isOpen_image_of_subset_source
    (Schoenflies.Plane.isOpen_openSquare 0 ρ₁) htρ₁
  have hUN : U⊆N₁.source := by
    rintro y ⟨v,hv,rfl⟩
    exact N₁.map_target (htρ₁ hv)
  let aa : C(Interval,S) := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
  have ha1U : aa 1∈U := by
    refine ⟨0,?_,?_⟩
    · simp [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,hρ₁]
    · change N₁.symm 0=(a 1).val
      rw [←hz₁,N₁.left_inv hp₁]
  obtain ⟨α,hα0,hα1,hαtail,hαpos⟩ :=
    actual_terminal_chart_clean_connector_positive_precontact aa C U N₁ hU ha1U hcircle
      (fun y hy => (hl₁ y (hsmall₁ hy)).2)
  let p₀ : Path (r₀ 1) (a 0).val :=
    (⟨r₀,rfl,rfl⟩ : Path (r₀ 0) (r₀ 1)).symm.cast rfl hzR₀.symm
  let p : Path (a 0).val (a 1).val := ⟨aa,rfl,rfl⟩
  let p₁ : Path (a 1).val (r₁ 1) :=
    (⟨r₁,rfl,rfl⟩ : Path (r₁ 0) (r₁ 1)).cast hzR₁.symm rfl
  have hhalf : r ⟨1/2,by norm_num⟩=(a 1).val := by
    rw [hrmid _ (by norm_num) (by norm_num)]
    norm_num
  have hrC := actual_extended_regional_connector_unique_middle_circle_contact F C
    (fun y hy => interior_subset (hCi hy)) a hcircle r₀ r₁ r hr hzR₀ hzR₁ hoR₀ hoffR₁ hrrange hhalf
  have hrneg : N₁ (p₁ 1) 0<0 := by
    change N₁ (r₁ 1) 0<0
    rw [hcoordR₁]
    norm_num
    linarith
  obtain ⟨Q,P,M,hQ,hP,hQB,hPB,hQI,hPI,hQC,hPC,hdQP,hMQ,hMP,hM₀,hM₁⟩ :=
    actual_three_clock_extended_connector_constructs_regional_rails_with_caps p₀ p p₁ r
      F B G C U₀ U hF hC hCi hfront hrinitial hrmid hrtail hU₀ ha₀U
      (fun t => hcap₀ (hpatchR₀ _)) hainside
      hiR₁ N₁ hU hUN α hα0 hα1 hαtail hpatchR₁ hαpos hrneg
      (fun y hy hz => (hl₁ y (hsmall₁ hy)).2.2.mpr hz) hrC EE hE
      (fun z => hEU (Set.mem_range_self z)) hcenter hrout
  have hPend : (P 1).val∈U := by rw [←hMP 1];exact hM₁ _
  have hQend : (Q 1).val∈U := by rw [←hMQ 1];exact hM₁ _
  have hne : (P 1).val≠(Q 1).val := by
    intro he
    exact Set.disjoint_left.mp hdQP (Set.mem_range_self 1) (he ▸ Set.mem_range_self 1)
  obtain ⟨k,hk,hk0,hk1,hkC,hkU⟩ :=
    actual_terminal_chart_axis_distinct_endpoints_short_curve_arc C N₁ ρ₁ htρ₁
      (fun y hy => (hl₁ y (hsmall₁ hy)).2.2) (P 1).val (Q 1).val hPend hQend
      ((hPC 1).mpr rfl) ((hQC 1).mpr rfl) hne
  exact ⟨P,Q,M,k,hP,hQ,hPB,hQB,hPI,hQI,hPC,hQC,hdQP.symm,hMP,hMQ,hM₀,
    fun w => hcap₁ (hM₁ w),hk,hk0,hk1,hkC,fun y hy => hcap₁ (hkU hy)⟩

private theorem actual_original_chart_closed_disk_ambient_cap_radius_enlargement
    {S : Type} [TopologicalSpace S]
    (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
    (center : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hR : 0<R)
    (htarget : Metric.closedBall center R⊆e.target) :
    ∃ R' : ℝ,R<R' ∧ Metric.closedBall center R'⊆e.target := by
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_closedBall center R).exists_cthickening_subset_open
    e.open_target htarget
  refine ⟨δ+R,by linarith,?_⟩
  rw [←cthickening_closedBall hδ.le hR.le center]
  exact hsub

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

/-- REVIEW ONLY: the actual nonempty bordered-arc fiber in the source comparison.
The distinguished boundary is the original chart-disk circle; all other actual
frontier components are original-S essential curves. No disk/annulus classifier,
connector, proper arc, surgery strip or filling is supplied as a premise. -/
theorem source_actual_region_essential_proper_arc
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] [Nonempty J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    ∃ a : C(Interval,↥F), Topology.IsEmbedding a ∧
      (a ⟨0,by norm_num⟩).val ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
      (a ⟨1,by norm_num⟩).val ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F) ∧
      ¬ (∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a ∪ Set.range b) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hSimpleConcat {X : Type} [TopologicalSpace X]
      {x y z : X} (γ : Path x y) (δ : Path y z)
      (hγ : Function.Injective γ) (hδ : Function.Injective δ)
      (hinter : Set.range γ ∩ Set.range δ = {y}) :
      Function.Injective (γ.trans δ) := by
    intro s t hst
    rw [Path.trans_apply, Path.trans_apply] at hst
    by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2 <;>
      simp only [dif_pos, hs, ht] at hst
    · have heq := hγ hst
      apply Subtype.ext
      have hval := congrArg Subtype.val heq
      dsimp at hval
      linarith
    · let a : unitInterval := ⟨2 * s,
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩
      let b : unitInterval := ⟨2 * t - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have hmem : γ a ∈ Set.range γ ∩ Set.range δ :=
        ⟨⟨a, rfl⟩, ⟨b, hst.symm⟩⟩
      have hjoin : γ a = y := by
        have : γ a ∈ ({y} : Set X) := hinter ▸ hmem
        simpa using this
      have ha : a = (1 : unitInterval) := hγ (hjoin.trans γ.target.symm)
      have hb : b = (0 : unitInterval) := hδ (hst.symm.trans (hjoin.trans δ.source.symm))
      apply Subtype.ext
      have ha' := congrArg Subtype.val ha
      have hb' := congrArg Subtype.val hb
      dsimp [a, b] at ha' hb'
      linarith
    · let a : unitInterval := ⟨2 * t,
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      let b : unitInterval := ⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩
      have hmem : γ a ∈ Set.range γ ∩ Set.range δ :=
        ⟨⟨a, rfl⟩, ⟨b, hst⟩⟩
      have hjoin : γ a = y := by
        have : γ a ∈ ({y} : Set X) := hinter ▸ hmem
        simpa using this
      have ha : a = (1 : unitInterval) := hγ (hjoin.trans γ.target.symm)
      have hb : b = (0 : unitInterval) := hδ (hst.trans (hjoin.trans δ.source.symm))
      apply Subtype.ext
      have ha' := congrArg Subtype.val ha
      have hb' := congrArg Subtype.val hb
      dsimp [a, b] at ha' hb'
      linarith
    · have heq := hδ hst
      apply Subtype.ext
      have hval := congrArg Subtype.val heq
      dsimp at hval
      linarith
  have hSimplePrefix {a b : S} (p : Path a b) (hp : Function.Injective p)
      (u : Interval) (hu : 0 < u) :
      ∃ r : Path a (p u), Function.Injective r ∧ Set.range r ⊆ Set.range p := by
    let clock : C(Interval,Interval) := {
      toFun := fun t => ⟨(u:ℝ)*(t:ℝ),by
        constructor <;> nlinarith [u.property.1,u.property.2,t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
    have hc0 : clock 0 = 0 := by apply Subtype.ext; change (u:ℝ)*0=0; ring
    have hc1 : clock 1 = u := by apply Subtype.ext; change (u:ℝ)*1=(u:ℝ); ring
    let r : Path a (p u) := {
      toFun := fun t => p (clock t)
      continuous_toFun := p.continuous.comp clock.continuous
      source' := by rw [hc0,p.source]
      target' := by rw [hc1] }
    refine ⟨r,?_,?_⟩
    · intro t s he
      have hv := congrArg Subtype.val (hp he)
      change (u:ℝ)*(t:ℝ)=(u:ℝ)*(s:ℝ) at hv
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt (show 0 < (u:ℝ) from hu)) hv)
    · rintro z ⟨t,rfl⟩
      exact ⟨clock t,rfl⟩
  have hSimpleJoin {a b d : S} (p : Path a b) (q : Path b d)
      (hp : Function.Injective p) (hq : Function.Injective q) (had : a ≠ d) :
      ∃ r : Path a d, Function.Injective r ∧
        Set.range r ⊆ Set.range p ∪ Set.range q := by
    by_cases hd : d ∈ Set.range p
    · obtain ⟨u,hu⟩ := hd
      have hu0 : 0 < u := by
        apply lt_of_le_of_ne u.property.1
        intro he
        have huZero : u = 0 := Subtype.ext he.symm
        exact had (by rw [huZero,p.source] at hu; exact hu)
      obtain ⟨r,hr,hsub⟩ := hSimplePrefix p hp u hu0
      exact ⟨r.cast rfl hu.symm,by simpa only [Path.cast_coe] using hr,
        (by simpa only [Path.cast_coe] using hsub.trans Set.subset_union_left)⟩
    · let T : Set Interval := q ⁻¹' Set.range p
      have hT : IsCompact T :=
        ((isCompact_range p.continuous).isClosed.preimage q.continuous).isCompact
      have hTne : T.Nonempty := ⟨0,by change q 0 ∈ Set.range p; rw [q.source]; exact ⟨1,p.target⟩⟩
      obtain ⟨s,hs,hmax⟩ := hT.exists_isGreatest hTne
      have hs1 : s < 1 := by
        apply lt_of_le_of_ne s.property.2
        intro he
        have hsOne : s = 1 := Subtype.ext he
        exact hd (by change q s ∈ Set.range p at hs; rw [hsOne,q.target] at hs; exact hs)
      obtain ⟨u,hu⟩ := hs
      let clock : C(Interval,Interval) := {
        toFun := fun t => ⟨(s:ℝ)+(1-(s:ℝ))*(t:ℝ),by
          constructor <;> nlinarith [s.property.1,s.property.2,t.property.1,t.property.2]⟩
        continuous_toFun := by fun_prop }
      have hc0 : clock 0 = s := by apply Subtype.ext; change (s:ℝ)+(1-(s:ℝ))*0=(s:ℝ); ring
      have hc1 : clock 1 = 1 := by apply Subtype.ext; change (s:ℝ)+(1-(s:ℝ))*1=1; ring
      let tail : Path (q s) d := {
        toFun := fun t => q (clock t)
        continuous_toFun := q.continuous.comp clock.continuous
        source' := by rw [hc0]
        target' := by rw [hc1,q.target] }
      have htinj : Function.Injective tail := by
        intro t v he
        have hv := congrArg Subtype.val (hq he)
        change (s:ℝ)+(1-(s:ℝ))*(t:ℝ)=(s:ℝ)+(1-(s:ℝ))*(v:ℝ) at hv
        apply Subtype.ext
        have hslt : (s:ℝ) < 1 := hs1
        nlinarith
      have htsub : Set.range tail ⊆ Set.range q := by
        rintro z ⟨t,rfl⟩
        exact ⟨clock t,rfl⟩
      have htavoid (t : Interval) (ht : 0 < t) : tail t ∉ Set.range p := by
        intro hh
        have hm : clock t ≤ s := hmax hh
        change (s:ℝ)+(1-(s:ℝ))*(t:ℝ) ≤ (s:ℝ) at hm
        have hslt : (s:ℝ) < 1 := hs1
        have htpos : 0 < (t:ℝ) := ht
        nlinarith
      by_cases hu0 : u = 0
      · have hqa : a = q s := by rw [← hu,hu0,p.source]
        exact ⟨tail.cast hqa rfl,by simpa only [Path.cast_coe] using htinj,
          (by simpa only [Path.cast_coe] using htsub.trans Set.subset_union_right)⟩
      · obtain ⟨r,hr,hsub⟩ := hSimplePrefix p hp u (lt_of_le_of_ne u.property.1 (Ne.symm hu0))
        let first : Path a (q s) := r.cast rfl hu.symm
        have hfinj : Function.Injective first := hr
        have hfsub : Set.range first ⊆ Set.range p := hsub
        have hinter : Set.range first ∩ Set.range tail = {q s} := by
          ext y
          constructor
          · rintro ⟨hy,⟨t,rfl⟩⟩
            by_cases ht : t = 0
            · simpa only [ht,Path.source,Set.mem_singleton_iff]
            · exact False.elim (htavoid t (lt_of_le_of_ne t.property.1 (Ne.symm ht)) (hfsub hy))
          · rintro rfl
            exact ⟨⟨1,first.target⟩,⟨0,tail.source⟩⟩
        refine ⟨first.trans tail,hSimpleConcat first tail hfinj htinj hinter,?_⟩
        rw [Path.trans_range]
        exact Set.union_subset_union hfsub htsub
  have hLocalSimpleArc (U : Set S) (hU : IsOpen U) (u : S) (hu : u ∈ U) :
      ∃ V : Set S, IsOpen V ∧ u ∈ V ∧ V ⊆ U ∧
        ∀ y ∈ V, u ≠ y → ∃ p : Path u y,
          Function.Injective p ∧ Set.range p ⊆ V := by
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) u
    have heu : u ∈ e.source := ChartedSpace.mem_chart_source u
    have heU : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
    have hcenter : e u ∈ e.target ∩ e.symm ⁻¹' U :=
      ⟨e.map_source heu,by simpa only [Set.mem_preimage,e.left_inv heu] using hu⟩
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp heU (e u) hcenter
    let B := Metric.ball (e u) r
    have hBt : B ⊆ e.target := fun z hz => (hball hz).1
    let V := e.symm '' B
    have hVu : u ∈ V := ⟨e u,Metric.mem_ball_self hr,e.left_inv heu⟩
    refine ⟨V,e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hBt,hVu,?_,?_⟩
    · rintro z ⟨w,hw,rfl⟩
      exact (hball hw).2
    · intro y hy hne
      obtain ⟨w,hw,hwy⟩ := hy
      have hew : e y = w := by rw [← hwy,e.right_inv (hBt hw)]
      let line := Path.segment (e u) w
      have hline (t : Interval) : line t ∈ B := by
        apply (convex_ball (e u) r).segment_subset (Metric.mem_ball_self hr) hw
        rw [← Path.range_segment]
        exact ⟨t,rfl⟩
      let p : Path u y := {
        toFun := fun t => e.symm (line t)
        continuous_toFun := e.symm.continuousOn.comp_continuous line.continuous
          (fun t => hBt (hline t))
        source' := by rw [line.source,e.left_inv heu]
        target' := by rw [line.target,hwy] }
      refine ⟨p,?_,?_⟩
      · intro t v heq
        apply Path.segment_injective_of_ne (show e u ≠ w from by
          intro he
          apply hne
          rw [← hwy,← he,e.left_inv heu])
        exact e.symm.injOn (hBt (hline t)) (hBt (hline v)) heq
      · rintro z ⟨t,rfl⟩
        exact ⟨line t,hline t,rfl⟩
  have hOpenRegionSimpleArc (U : Set S) (hU : IsOpen U) (hUc : IsPreconnected U)
      (a b : S) (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) :
      ∃ p : Path a b, Function.Injective p ∧ Set.range p ⊆ U := by
    let R : S → S → Prop := fun u v => u = v ∨
      ∃ p : Path u v, Function.Injective p ∧ Set.range p ⊆ U
    have hsymm {u v : S} : R u v → R v u := by
      rintro (he | ⟨p,hp,hsub⟩)
      · exact Or.inl he.symm
      · refine Or.inr ⟨p.symm,?_,?_⟩
        · exact hp.comp unitInterval.symm_involutive.injective
        · simpa only [Path.symm_range] using hsub
    have htrans {u v w : S} : R u v → R v w → R u w := by
      rintro (he | ⟨p,hp,hsub⟩) (he' | ⟨q,hq,hsub'⟩)
      · exact Or.inl (he.trans he')
      · subst v
        exact Or.inr ⟨q,hq,hsub'⟩
      · subst w
        exact Or.inr ⟨p,hp,hsub⟩
      · by_cases huw : u = w
        · exact Or.inl huw
        · obtain ⟨r,hr,hrsub⟩ := hSimpleJoin p q hp hq huw
          exact Or.inr ⟨r,hr,hrsub.trans (Set.union_subset hsub hsub')⟩
    let A : Set S := {y | y ∈ U ∧ R a y}
    have hAopen : IsOpen A := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      obtain ⟨V,hV,hyV,hVU,hpaths⟩ := hLocalSimpleArc U hU y hy.1
      refine ⟨V,?_,hV,hyV⟩
      intro z hz
      refine ⟨hVU hz,htrans hy.2 ?_⟩
      by_cases hyz : y = z
      · exact Or.inl hyz
      · obtain ⟨p,hp,hsub⟩ := hpaths z hz hyz
        exact Or.inr ⟨p,hp,hsub.trans hVU⟩
    have hOtherOpen : IsOpen (U \ A) := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      obtain ⟨V,hV,hyV,hVU,hpaths⟩ := hLocalSimpleArc U hU y hy.1
      refine ⟨V,?_,hV,hyV⟩
      intro z hz
      refine ⟨hVU hz,?_⟩
      intro hzA
      apply hy.2
      refine ⟨hy.1,htrans hzA.2 (hsymm ?_)⟩
      by_cases hyz : y = z
      · exact Or.inl hyz
      · obtain ⟨p,hp,hsub⟩ := hpaths z hz hyz
        exact Or.inr ⟨p,hp,hsub.trans hVU⟩
    have hcover : U ⊆ A ∪ (U \ A) := by
      intro y hy
      by_cases hyA : y ∈ A
      · exact Or.inl hyA
      · exact Or.inr ⟨hy,hyA⟩
    have hnonempty : (U ∩ A).Nonempty := ⟨a,ha,ha,Or.inl rfl⟩
    have hall : U ⊆ A := hUc.subset_left_of_subset_union hAopen hOtherOpen
      (Set.disjoint_left.mpr (fun y hy hy' => hy'.2 hy)) hcover hnonempty
    rcases (hall hb).2 with he | hp
    · exact False.elim (hab he)
    · exact hp
  have hFclosed : IsClosed F := hFcompact.isClosed
  have hActualFrontierCirclesInRegion (j : J) : (c j).val.image ⊆ F := by
    intro y hy
    have hyfront : y ∈ frontier F := by
      rw [hfrontier]
      exact Or.inr (Set.mem_iUnion.mpr ⟨j,hy⟩)
    exact hFclosed.closure_eq ▸ frontier_subset_closure hyfront
  have hActualRegionInteriorNonempty : (interior F).Nonempty := by
    have hFne : F.Nonempty := ⟨(c (Classical.choice (inferInstance : Nonempty J))).val.map 1,
      hActualFrontierCirclesInRegion _ (Set.mem_range_self 1)⟩
    by_contra he
    have hIE : interior F = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    rw [hIE,closure_empty] at hregular
    exact hFne.ne_empty hregular.symm
  have hActualRegionNotInDisk
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
      (hd : Topology.IsEmbedding d) : ¬ F ⊆ Set.range d := by
    intro hsub
    let j : J := Classical.choice inferInstance
    obtain ⟨e,he,hboundary,hinside⟩ :=
      CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
        (c j).val d hd ((hActualFrontierCirclesInRegion j).trans hsub)
    exact (c j).property ⟨e,he,hboundary⟩
  have hActualChartBoundaryCurve
      (x : S) (R : ℝ) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
      ∃ b : Curve S,b.image=(chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R := by
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
    let L := LeanEval.Topology.ClassificationOfSurfaces.Moise.planeComplexIsometry
    let φ : Circle → EuclideanSpace ℝ (Fin 2) := fun z => e x + R • L.symm (z:ℂ)
    have hφc : Continuous φ := by
      dsimp [φ]
      fun_prop
    have hφsphere (z : Circle) : φ z ∈ Metric.sphere (e x) R := by
      rw [Metric.mem_sphere,dist_eq_norm]
      change ‖e x + R • L.symm (z:ℂ) - e x‖=R
      rw [add_sub_cancel_left,norm_smul,LinearIsometryEquiv.norm_map,Circle.norm_coe]
      simp [Real.norm_of_nonneg hR.le]
    have hφtarget (z : Circle) : φ z ∈ e.target := htarget (Metric.sphere_subset_closedBall (hφsphere z))
    have hφi : Function.Injective φ := by
      intro z w h
      have hs : R • L.symm (z:ℂ)=R • L.symm (w:ℂ) := add_left_cancel h
      have hl : L.symm (z:ℂ)=L.symm (w:ℂ) := (smul_right_injective _ (ne_of_gt hR)) hs
      exact Subtype.ext (L.symm.injective hl)
    let f : C(Circle,S) := ⟨fun z => e.symm (φ z),
      e.symm.continuousOn.comp_continuous hφc hφtarget⟩
    have hf : Topology.IsEmbedding f := (f.continuous.isClosedEmbedding (by
      intro z w h
      exact hφi (e.symm.injOn (hφtarget z) (hφtarget w) h))).isEmbedding
    refine ⟨⟨f,hf⟩,?_⟩
    apply Set.Subset.antisymm
    · rintro y ⟨z,rfl⟩
      exact ⟨φ z,hφsphere z,rfl⟩
    · rintro y ⟨v,hv,rfl⟩
      let u := R⁻¹ • (v-e x)
      have hu : ‖u‖=1 := by
        dsimp [u]
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR.le),← dist_eq_norm,Metric.mem_sphere.mp hv]
        exact inv_mul_cancel₀ (ne_of_gt hR)
      let z : Circle := ⟨L u,by
        apply mem_sphere_zero_iff_norm.mpr
        rw [LinearIsometryEquiv.norm_map,hu]⟩
      have hφ : φ z = v := by
        dsimp [φ,z]
        rw [L.symm_apply_apply]
        dsimp [u]
        rw [smul_inv_smul₀ (ne_of_gt hR)]
        abel
      exact ⟨z,congrArg e.symm hφ⟩
  have hActualLocalSecondAxisInteriorPreconnected (S : Type) [TopologicalSpace S]
      (E : OpenPartialHomeomorph S Schoenflies.Plane) (F : Set S)
      (hF : IsClosed F) (p : S) (hp : p∈E.source) (hEp : E p=0)
      (hpfront : p∈frontier F) (r : ℝ) (hr : 0<r)
      (htarget : Schoenflies.Plane.openSquare 0 r ⊆ E.target)
      (hfrontier : ∀ y∈E.source,y∈frontier F ↔ E y 1=0) :
      IsPreconnected ((E.symm '' Schoenflies.Plane.openSquare 0 r) ∩ interior F) := by
    classical
    let P : Set Schoenflies.Plane := Schoenflies.Plane.openSquare 0 r ∩ {z : Schoenflies.Plane | 0<z 1}
    let M : Set Schoenflies.Plane := Schoenflies.Plane.openSquare 0 r ∩ {z : Schoenflies.Plane | z 1<0}
    have hconvP : Convex ℝ P := by
      intro x hx z hz a b ha hb hab
      refine ⟨(Schoenflies.Plane.convex_openSquare 0 r) hx.1 hz.1 ha hb hab,?_⟩
      change 0<(a • x+b • z) 1
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      have hx1 : 0<x 1 := hx.2
      have hz1 : 0<z 1 := hz.2
      by_cases ha0 : a=0
      · have hb1 : b=1 := by linarith
        simpa [ha0,hb1] using hz1
      · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx1)
          (mul_nonneg hb hz1.le)
    have hconvM : Convex ℝ M := by
      intro x hx z hz a b ha hb hab
      refine ⟨(Schoenflies.Plane.convex_openSquare 0 r) hx.1 hz.1 ha hb hab,?_⟩
      change (a • x+b • z) 1<0
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      have hx1 : x 1<0 := hx.2
      have hz1 : z 1<0 := hz.2
      by_cases ha0 : a=0
      · have hb1 : b=1 := by linarith
        simpa [ha0,hb1] using hz1
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (lt_of_le_of_ne ha (Ne.symm ha0)) hx1)
          (mul_nonpos_of_nonneg_of_nonpos hb hz1.le)
    have hPconn : IsPreconnected (E.symm '' P) := hconvP.isPreconnected.image E.symm
      (E.continuousOn_symm.mono (fun z hz => htarget hz.1))
    have hMconn : IsPreconnected (E.symm '' M) := hconvM.isPreconnected.image E.symm
      (E.continuousOn_symm.mono (fun z hz => htarget hz.1))
    have hPavoid : Disjoint (E.symm '' P) (frontier F) := by
      apply Set.disjoint_left.mpr
      rintro w ⟨z,hz,rfl⟩ hw
      have he := (hfrontier _ (E.map_target (htarget hz.1))).mp hw
      rw [E.right_inv (htarget hz.1)] at he
      exact (ne_of_gt hz.2) he
    have hMavoid : Disjoint (E.symm '' M) (frontier F) := by
      apply Set.disjoint_left.mpr
      rintro w ⟨z,hz,rfl⟩ hw
      have he := (hfrontier _ (E.map_target (htarget hz.1))).mp hw
      rw [E.right_inv (htarget hz.1)] at he
      exact (ne_of_lt hz.2) he
    let C := E.symm '' Schoenflies.Plane.openSquare 0 r
    have hC : IsOpen C := E.symm.isOpen_image_of_subset_source
      (Schoenflies.Plane.isOpen_openSquare 0 r) htarget
    have hpC : p∈C := by
      refine ⟨0,?_,?_⟩
      · simp [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,hr]
      · rw [←hEp,E.left_inv hp]
    have hzero (z : Schoenflies.Plane) (hz : z∈Schoenflies.Plane.openSquare 0 r)
        (hz0 : z 1=0) : E.symm z∈frontier F :=
      (hfrontier _ (E.map_target (htarget hz))).mpr (by rw [E.right_inv (htarget hz)]; exact hz0)
    have hsplit (y : S) (hy : y∈C ∩ interior F) :
        y∈E.symm '' P ∨ y∈E.symm '' M := by
      obtain ⟨⟨z,hz,hzy⟩,hyI⟩ := hy
      have hz0 : z 1≠0 := by
        intro he
        exact Set.disjoint_left.mp disjoint_interior_frontier hyI (hzy ▸ hzero z hz he)
      rcases lt_or_gt_of_ne hz0 with hn | hp
      · exact Or.inr ⟨z,⟨hz,hn⟩,hzy⟩
      · exact Or.inl ⟨z,⟨hz,hp⟩,hzy⟩
    rcases connected_cap_side F (E.symm '' P) hPconn hPavoid with hPin | hPout <;>
      rcases connected_cap_side F (E.symm '' M) hMconn hMavoid with hMin | hMout
    · have hCF : C ⊆ F := by
        rintro y ⟨z,hz,rfl⟩
        rcases lt_trichotomy (z 1) 0 with hn | he | hp'
        · exact interior_subset (hMin ⟨z,⟨hz,hn⟩,rfl⟩)
        · exact hF.closure_eq ▸ frontier_subset_closure (hzero z hz he)
        · exact interior_subset (hPin ⟨z,⟨hz,hp'⟩,rfl⟩)
      have hpI : p∈interior F := interior_maximal hCF hC hpC
      exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hpI hpfront)
    · have heq : C ∩ interior F=E.symm '' P := by
        apply Set.Subset.antisymm
        · intro y hy
          rcases hsplit y hy with hp' | hm
          · exact hp'
          · exact False.elim ((interior_subset (hMout hm)) (interior_subset hy.2))
        · rintro y ⟨z,hz,rfl⟩
          exact ⟨⟨z,hz.1,rfl⟩,hPin ⟨z,hz,rfl⟩⟩
      exact heq.symm ▸ hPconn
    · have heq : C ∩ interior F=E.symm '' M := by
        apply Set.Subset.antisymm
        · intro y hy
          rcases hsplit y hy with hp' | hm
          · exact False.elim ((interior_subset (hPout hp')) (interior_subset hy.2))
          · exact hm
        · rintro y ⟨z,hz,rfl⟩
          exact ⟨⟨z,hz.1,rfl⟩,hMin ⟨z,hz,rfl⟩⟩
      exact heq.symm ▸ hMconn
    · have heq : C ∩ interior F=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        rcases hsplit y hy with hp' | hm
        · exact (interior_subset (hPout hp')) (interior_subset hy.2)
        · exact (interior_subset (hMout hm)) (interior_subset hy.2)
      exact heq.symm ▸ isPreconnected_empty
  have hActualFiniteFrontierLocalInterior (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
      (F : Set S) (hF : IsClosed F) (K : Type) [Fintype K]
      (c : K → Curve S) (hdis : ∀ i j,i≠j → Disjoint (c i).image (c j).image)
      (hfront : frontier F=⋃ i,(c i).image) (p : S) (hp : p∈frontier F) :
      ∃ U : Set S,IsOpen U ∧ p∈U ∧ IsPreconnected (U ∩ interior F) := by
    classical
    obtain ⟨i,hpi⟩ := Set.mem_iUnion.mp (hfront ▸ hp)
    let B : Set S := ⋃ j,⋃ (_ : j≠i),(c j).image
    have hB : IsCompact B := isCompact_iUnion (fun j =>
      isCompact_iUnion (fun _ => isCompact_range (c j).embedded.continuous))
    have hpB : p∉B := by
      change p∉⋃ j,⋃ (_ : j≠i),(c j).image
      simp only [Set.mem_iUnion]
      rintro ⟨j,hji,hpj⟩
      exact Set.disjoint_left.mp (hdis j i hji) hpj hpi
    obtain ⟨E,hpE,hEp,hEB,hEt,hEaxis⟩ :=
      CurveComplex.PositionUniverseV2.position_curve_crosscut_chart S (c i) p hpi
        Bᶜ hB.isClosed.isOpen_compl hpB
    have hfrontE : ∀ y∈E.source,y∈frontier F ↔ E y 1=0 := by
      intro y hy
      rw [←hEaxis y hy,hfront]
      constructor
      · intro hf
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hf
        by_cases hji : j=i
        · simpa only [hji] using hj
        · exact False.elim (hEB hy (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hji,hj⟩⟩))
      · exact fun hi => Set.mem_iUnion.mpr ⟨i,hi⟩
    have ht : Schoenflies.Plane.openSquare 0 (1/2:ℝ) ⊆ E.target := by
      intro z hz
      apply hEt
      change Schoenflies.Plane.supDist z 0≤1
      change Schoenflies.Plane.supDist z 0<1/2 at hz
      linarith
    let U := E.symm '' Schoenflies.Plane.openSquare 0 (1/2:ℝ)
    have hU : IsOpen U := E.symm.isOpen_image_of_subset_source
      (Schoenflies.Plane.isOpen_openSquare _ _) ht
    have hpU : p∈U := by
      refine ⟨0,?_,?_⟩
      · norm_num [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm]
      · rw [←hEp,E.left_inv hpE]
    exact ⟨U,hU,hpU,hActualLocalSecondAxisInteriorPreconnected S E F hF p hpE hEp hp
      (1/2) (by norm_num) ht hfrontE⟩
  have hRegularRegionConnectedInterior (X : Type) [TopologicalSpace X] (F : Set X)
      (hF : IsPreconnected F) (hregular : closure (interior F)=F)
      (hlocal : ∀ y∈F,∃ N : Set X,IsOpen N ∧ y∈N ∧ IsPreconnected (N ∩ interior F)) :
      IsPreconnected (interior F) := by
    intro U V hU hV hcover hUne hVne
    by_contra hn
    let A := interior F ∩ U
    let B := interior F ∩ V
    have hsplit : interior F=A ∪ B := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hcover hx with hu | hv
        · exact Or.inl ⟨hx,hu⟩
        · exact Or.inr ⟨hx,hv⟩
      · exact fun x hx => hx.elim And.left And.left
    have hFcover : F ⊆ closure A ∪ closure B := by
      rw [←hregular,hsplit,closure_union]
    have hFA : (F ∩ closure A).Nonempty := by
      obtain ⟨x,hx,hxu⟩ := hUne
      exact ⟨x,interior_subset hx,subset_closure ⟨hx,hxu⟩⟩
    have hFB : (F ∩ closure B).Nonempty := by
      obtain ⟨x,hx,hxv⟩ := hVne
      exact ⟨x,interior_subset hx,subset_closure ⟨hx,hxv⟩⟩
    obtain ⟨y,hyF,hyA,hyB⟩ := isPreconnected_closed_iff.mp hF
      (closure A) (closure B) isClosed_closure isClosed_closure hFcover hFA hFB
    obtain ⟨N,hN,hyN,hNconn⟩ := hlocal y hyF
    obtain ⟨u,huN,huA⟩ := (mem_closure_iff_nhds.mp hyA) N (hN.mem_nhds hyN)
    obtain ⟨v,hvN,hvB⟩ := (mem_closure_iff_nhds.mp hyB) N (hN.mem_nhds hyN)
    have hNcover : N ∩ interior F ⊆ U ∪ V := fun x hx => hcover hx.2
    obtain ⟨z,hzN,hzU,hzV⟩ := hNconn U V hU hV hNcover
      ⟨u,⟨huN,huA.1⟩,huA.2⟩ ⟨v,⟨hvN,hvB.1⟩,hvB.2⟩
    exact hn ⟨z,hzN.2,hzU,hzV⟩
  have hActualRegionInteriorConnected : IsConnected (interior F) := by
    letI : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace
      (EuclideanSpace ℝ (Fin 2)) S
    obtain ⟨b,hb⟩ := hActualChartBoundaryCurve x R hR htarget
    let d : Option J → Curve S := fun k => k.elim b (fun j => (c j).val)
    have hd : ∀ i j,i≠j → Disjoint (d i).image (d j).image := by
      intro i j hij
      cases i with
      | none =>
        cases j with
        | none => exact False.elim (hij rfl)
        | some j => simpa [d,hb] using (hbaseDisjoint j).symm
      | some i =>
        cases j with
        | none => simpa [d,hb] using hbaseDisjoint i
        | some j =>
          exact hdisjoint i j (fun he => hij (congrArg Option.some he))
    have hfrontD : frontier F=⋃ k,(d k).image := by
      ext y
      rw [hfrontier]
      constructor
      · rintro (hb' | hc')
        · exact Set.mem_iUnion.mpr ⟨none,by simpa [d,hb] using hb'⟩
        · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hc'
          exact Set.mem_iUnion.mpr ⟨some j,hj⟩
      · intro hd'
        obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hd'
        cases k with
        | none => exact Or.inl (by simpa [d,hb] using hk)
        | some j => exact Or.inr (Set.mem_iUnion.mpr ⟨j,hk⟩)
    have hlocal : ∀ y∈F,∃ U : Set S,IsOpen U ∧ y∈U ∧
        IsPreconnected (U ∩ interior F) := by
      intro y hy
      by_cases hi : y∈interior F
      · let U := connectedComponentIn (interior F) y
        have hU : IsOpen U := isOpen_interior.connectedComponentIn
        have hyU : y∈U := mem_connectedComponentIn hi
        have hUI : U ∩ interior F=U := Set.inter_eq_left.mpr (connectedComponentIn_subset _ _)
        exact ⟨U,hU,hyU,hUI.symm ▸ isPreconnected_connectedComponentIn⟩
      · exact hActualFiniteFrontierLocalInterior S F hFclosed (Option J) d hd hfrontD y
          ((mem_frontier_iff_notMem_interior hy).mpr hi)
    exact ⟨hActualRegionInteriorNonempty,
      hRegularRegionConnectedInterior S F hFconnected.isPreconnected hregular hlocal⟩
  have hcollarInNeighborhood (b : EssentialCurve S) (N : Set S)
      (hN : IsOpen N) (hbN : b.val.image ⊆ N) :
      ∃ (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (U : Set (Set.Ioo (-1 : ℝ) 1)),
        Topology.IsOpenEmbedding E ∧
        (∀ w, E (⟨0, by norm_num⟩, w) = b.val.map w) ∧
        IsOpen U ∧ (⟨0, by norm_num⟩ : Set.Ioo (-1 : ℝ) 1) ∈ U ∧
        E '' (U ×ˢ Set.univ) ⊆ N := by
    obtain ⟨E, hE, hcore⟩ :=
      CurveComplex.LocalSurgery.actual_original_essential_circle_has_annular_collar
        S g hg hS b
    have hprod : ({⟨0, by norm_num⟩} : Set (Set.Ioo (-1 : ℝ) 1)) ×ˢ
        (Set.univ : Set Circle) ⊆ E ⁻¹' N := by
      rintro ⟨t, w⟩ ⟨ht, hw⟩
      have ht0 : t = ⟨0, by norm_num⟩ := Set.mem_singleton_iff.mp ht
      change E (t, w) ∈ N
      rw [ht0, hcore]
      exact hbN (Set.mem_range_self w)
    obtain ⟨U, V, hU, hV, hzero, huniv, hUV⟩ := generalized_tube_lemma
      isCompact_singleton isCompact_univ (hN.preimage E.continuous) hprod
    refine ⟨E, U, hE, hcore, hU, hzero (Set.mem_singleton _), ?_⟩
    rintro y ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
    exact hUV ⟨ht, huniv (Set.mem_univ w)⟩
  have hcollarThin (b : EssentialCurve S) (N : Set S)
      (hN : IsOpen N) (hbN : b.val.image ⊆ N) :
      ∃ (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (δ : ℝ),
        Topology.IsOpenEmbedding E ∧
        (∀ w, E (⟨0, by norm_num⟩, w) = b.val.map w) ∧
        0 < δ ∧ δ < 1 ∧
        ∀ (t : Set.Ioo (-1 : ℝ) 1) (w : Circle), |(t : ℝ)| ≤ δ → E (t, w) ∈ N := by
    obtain ⟨E, U, hE, hcore, hU, hzero, hEN⟩ := hcollarInNeighborhood b N hN hbN
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU _ hzero
    let δ := min (ε / 2) (1 / 2)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨E, δ, hE, hcore, hδ, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    intro t w ht
    apply hEN
    refine ⟨(t, w), ⟨hεU ?_, Set.mem_univ _⟩, rfl⟩
    change dist (t : ℝ) (0 : ℝ) < ε
    simpa only [Real.dist_eq, sub_zero] using lt_of_le_of_lt ht hδε
  have hActualCollarInteriorSide (S : Type) [TopologicalSpace S]
      (F : Set S) (hreg : closure (interior F)=F)
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle,S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
      (hcoreF : ∀ w,E (⟨0,by norm_num⟩,w)∈F)
      (hfront : ∀ (t : Set.Ioo (-1 : ℝ) 1) (w : Circle), |(t : ℝ)|<δ → (E (t,w)∈frontier F ↔ (t : ℝ)=0)) :
      (∀ (t : Set.Ioo (-1 : ℝ) 1) (w : Circle), 0<(t : ℝ) → (t : ℝ)<δ → E (t,w)∈interior F) ∨
      (∀ (t : Set.Ioo (-1 : ℝ) 1) (w : Circle), -δ<(t : ℝ) → (t : ℝ)<0 → E (t,w)∈interior F) := by
    classical
    let z : Set.Ioo (-1 : ℝ) 1 := ⟨0,by norm_num⟩
    let p : Set.Ioo (-1 : ℝ) 1 := ⟨δ,by constructor <;> linarith⟩
    let m : Set.Ioo (-1 : ℝ) 1 := ⟨-δ,by constructor <;> linarith⟩
    let P := (Set.Ioo z p) ×ˢ (Set.univ : Set Circle)
    let M := (Set.Ioo m z) ×ˢ (Set.univ : Set Circle)
    let C := (Set.Ioo m p) ×ˢ (Set.univ : Set Circle)
    have hPi : IsPreconnected (Set.Ioo z p) := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      have he : Subtype.val '' Set.Ioo z p = Set.Ioo (0 : ℝ) δ := by
        ext t
        constructor
        · rintro ⟨t,ht,rfl⟩; exact ht
        · intro ht
          exact ⟨⟨t,by constructor <;> linarith [ht.1,ht.2]⟩,ht,rfl⟩
      rw [he]
      exact isPreconnected_Ioo
    have hMi : IsPreconnected (Set.Ioo m z) := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      have he : Subtype.val '' Set.Ioo m z = Set.Ioo (-δ) (0 : ℝ) := by
        ext t
        constructor
        · rintro ⟨t,ht,rfl⟩; exact ht
        · intro ht
          exact ⟨⟨t,by constructor <;> linarith [ht.1,ht.2]⟩,ht,rfl⟩
      rw [he]
      exact isPreconnected_Ioo
    have hPc : IsPreconnected (E '' P) :=
      (hPi.prod isPreconnected_univ).image E E.continuous.continuousOn
    have hMc : IsPreconnected (E '' M) :=
      (hMi.prod isPreconnected_univ).image E E.continuous.continuousOn
    have hPa : Disjoint (E '' P) (frontier F) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨⟨t,w⟩,ht,rfl⟩ hy
      have ht0 : 0<(t : ℝ) := ht.1.1
      have htd : (t : ℝ)<δ := ht.1.2
      exact (ne_of_gt ht0) ((hfront t w (abs_lt.mpr ⟨by linarith,htd⟩)).mp hy)
    have hMa : Disjoint (E '' M) (frontier F) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨⟨t,w⟩,ht,rfl⟩ hy
      have ht0 : (t : ℝ)<0 := ht.1.2
      have htd : -δ<(t : ℝ) := ht.1.1
      exact (ne_of_lt ht0) ((hfront t w (abs_lt.mpr ⟨htd,by linarith⟩)).mp hy)
    rcases connected_cap_side F (E '' P) hPc hPa with hPin | hPout
    · exact Or.inl (fun t w ht0 htd => hPin ⟨(t,w),⟨⟨ht0,htd⟩,Set.mem_univ _⟩,rfl⟩)
    rcases connected_cap_side F (E '' M) hMc hMa with hMin | hMout
    · exact Or.inr (fun t w htd ht0 => hMin ⟨(t,w),⟨⟨htd,ht0⟩,Set.mem_univ _⟩,rfl⟩)
    have hC : IsOpen (E '' C) := hE.isOpenMap C (isOpen_Ioo.prod isOpen_univ)
    let w : Circle := 1
    have hzC : E (z,w)∈E '' C := ⟨(z,w),⟨⟨by change -δ<0; linarith,by change 0<δ; exact hδ⟩,Set.mem_univ _⟩,rfl⟩
    have hzcl : E (z,w)∈closure (interior F) := hreg.symm ▸ hcoreF w
    obtain ⟨y,hyC,hyI⟩ := (mem_closure_iff_nhds.mp hzcl) (E '' C) (hC.mem_nhds hzC)
    obtain ⟨⟨t,v⟩,ht,rfl⟩ := hyC
    have htd : -δ<(t : ℝ) ∧ (t : ℝ)<δ := ht.1
    rcases lt_trichotomy (t : ℝ) 0 with hn | he | hp
    · exact False.elim ((interior_subset (hMout ⟨(t,v),⟨⟨htd.1,hn⟩,Set.mem_univ _⟩,rfl⟩))
        (interior_subset hyI))
    · exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hyI
        ((hfront t v (abs_lt.mpr htd)).mpr he))
    · exact False.elim ((interior_subset (hPout ⟨(t,v),⟨⟨hp,htd.2⟩,Set.mem_univ _⟩,rfl⟩))
        (interior_subset hyI))
  have hActualEssentialFrontierInteriorSide (F : Set S) (hF : IsClosed F)
      (hreg : closure (interior F)=F) (b : EssentialCurve S)
      (K : Set S) (hK : IsCompact K) (hBK : Disjoint b.val.image K)
      (hfront : frontier F=b.val.image ∪ K) :
      ∃ (E : C(Set.Ioo (-1 : ℝ) 1 × Circle,S)) (δ : ℝ),
        Topology.IsOpenEmbedding E ∧
        (∀ w,E (⟨0,by norm_num⟩,w)=b.val.map w) ∧
        0<δ ∧ δ<1 ∧
        ((∀ (t : Set.Ioo (-1 : ℝ) 1) w,0<(t : ℝ) → (t : ℝ)<δ → E (t,w)∈interior F) ∨
        (∀ (t : Set.Ioo (-1 : ℝ) 1) w,-δ<(t : ℝ) → (t : ℝ)<0 → E (t,w)∈interior F)) := by
    have hbN : b.val.image ⊆ Kᶜ := Set.disjoint_left.mp hBK
    obtain ⟨E,δ,hE,hcore,hδ,hδ1,hclear⟩ := hcollarThin b Kᶜ hK.isClosed.isOpen_compl hbN
    have hcoreF : ∀ w,E (⟨0,by norm_num⟩,w)∈F := by
      intro w
      apply hF.frontier_subset
      rw [hfront,hcore]
      exact Or.inl (Set.mem_range_self w)
    have hlocalfront : ∀ (t : Set.Ioo (-1 : ℝ) 1) w, |(t : ℝ)|<δ →
        (E (t,w)∈frontier F ↔ (t : ℝ)=0) := by
      intro t w ht
      rw [hfront]
      constructor
      · rintro (hb | hK')
        · obtain ⟨v,hv⟩ := hb
          have he : E (t,w)=E (⟨0,by norm_num⟩,v) := hv.symm.trans (hcore v).symm
          have hp := hE.injective he
          exact congrArg (fun z : Set.Ioo (-1 : ℝ) 1 × Circle => (z.1 : ℝ)) hp
        · exact False.elim (hclear t w ht.le hK')
      · intro ht0
        have ht' : t=⟨0,by norm_num⟩ := Subtype.ext ht0
        rw [ht',hcore]
        exact Or.inl (Set.mem_range_self w)
    exact ⟨E,δ,hE,hcore,hδ,hδ1,hActualCollarInteriorSide S F hreg E hE δ hδ hδ1 hcoreF hlocalfront⟩
  have hActualRetainedFrontierInteriorCollar (j : J) :
      ∃ (E : C(Set.Ioo (-1 : ℝ) 1 × Circle,S)) (δ : ℝ),
        Topology.IsOpenEmbedding E ∧
        (∀ w,E (⟨0,by norm_num⟩,w)=(c j).val.map w) ∧
        0<δ ∧ δ<1 ∧
        ((∀ (t : Set.Ioo (-1 : ℝ) 1) w,0<(t : ℝ) → (t : ℝ)<δ → E (t,w)∈interior F) ∨
        (∀ (t : Set.Ioo (-1 : ℝ) 1) w,-δ<(t : ℝ) → (t : ℝ)<0 → E (t,w)∈interior F)) := by
    obtain ⟨b,hb⟩ := hActualChartBoundaryCurve x R hR htarget
    let K : Set S := b.image ∪ ⋃ i,⋃ (_ : i≠j),(c i).val.image
    have hK : IsCompact K := (isCompact_range b.embedded.continuous).union
      (isCompact_iUnion (fun i => isCompact_iUnion
        (fun _ => isCompact_range (c i).val.embedded.continuous)))
    have hBK : Disjoint (c j).val.image K := by
      apply Set.disjoint_left.mpr
      intro y hy hyK
      rcases hyK with hyb | hyo
      · exact Set.disjoint_left.mp (hbaseDisjoint j) hy (hb ▸ hyb)
      · simp only [Set.mem_iUnion] at hyo
        obtain ⟨i,hij,hyi⟩ := hyo
        exact Set.disjoint_left.mp (hdisjoint j i (Ne.symm hij)) hy hyi
    have hfront : frontier F=(c j).val.image ∪ K := by
      rw [hfrontier,←hb]
      ext y
      constructor
      · rintro (hyb | hyo)
        · exact Or.inr (Or.inl hyb)
        · obtain ⟨i,hyi⟩ := Set.mem_iUnion.mp hyo
          by_cases hij : i=j
          · exact Or.inl (hij ▸ hyi)
          · exact Or.inr (Or.inr (Set.mem_iUnion.mpr
              ⟨i,Set.mem_iUnion.mpr ⟨hij,hyi⟩⟩))
      · rintro (hyj | hyb | hyo)
        · exact Or.inr (Set.mem_iUnion.mpr ⟨j,hyj⟩)
        · exact Or.inl hyb
        · simp only [Set.mem_iUnion] at hyo
          obtain ⟨i,_,hyi⟩ := hyo
          exact Or.inr (Set.mem_iUnion.mpr ⟨i,hyi⟩)
    exact hActualEssentialFrontierInteriorSide F hFclosed hregular (c j) K hK hBK hfront
  have hwidthSlide (ρ a : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (ha : |a| < ρ) :
      ∃ H : AmbientIsotopy (Set.Ioo (-1 : ℝ) 1 × Circle),
        (∀ w, H.finalMap (⟨0, by norm_num⟩, w) =
          (⟨a, by constructor <;> linarith [(abs_lt.mp ha).1, (abs_lt.mp ha).2]⟩, w)) ∧
        ∀ t z, ρ ≤ |(z.1 : ℝ)| → H.map (t,z) = z := by
    let bump : ℝ → ℝ := fun x => max (ρ - |x|) 0
    let f : Interval → ℝ → ℝ := fun t x => x + ((t : ℝ) * a / ρ) * bump x
    have hf : Continuous (fun z : Interval × ℝ => f z.1 z.2) := by
      dsimp [f, bump]
      fun_prop
    have hfix (t : Interval) (x : ℝ) (hx : ρ ≤ |x|) : f t x = x := by
      simp [f, bump, max_eq_right (sub_nonpos.mpr hx)]
    have hmono (t : Interval) : StrictMono (f t) := by
      have hs : |(t : ℝ) * a / ρ| < 1 := by
        rw [abs_div, abs_mul, abs_of_nonneg t.property.1, abs_of_pos hρ]
        apply (div_lt_one hρ).mpr
        nlinarith [t.property.2, abs_nonneg a]
      intro x y hxy
      have hb : |bump y - bump x| ≤ y - x := by
        calc
          |bump y - bump x| ≤ |(ρ - |y|) - (ρ - |x|)| := abs_max_sub_max_le_abs _ _ _
          _ = abs (abs y - abs x) := by
            rw [show (ρ - |y|) - (ρ - |x|) = -(|y| - |x|) by ring, abs_neg]
          _ ≤ |y - x| := abs_abs_sub_abs_le_abs_sub y x
          _ = y - x := abs_of_pos (sub_pos.mpr hxy)
      have hprod := mul_le_mul_of_nonneg_left hb (abs_nonneg ((t : ℝ)*a/ρ))
      have hneg := neg_abs_le (((t : ℝ)*a/ρ) * (bump y - bump x))
      rw [abs_mul] at hneg
      dsimp [f]
      nlinarith [sub_pos.mpr hxy]
    have hsurj (t : Interval) : Function.Surjective (f t) := by
      intro y
      let L := min y (-ρ)
      let U := max y ρ
      have hL : ρ ≤ |L| := by
        have hh : L ≤ -ρ := min_le_right _ _
        linarith [neg_le_abs L]
      have hU : ρ ≤ |U| := (le_max_right _ _).trans (le_abs_self U)
      have hLU : L ≤ U := (min_le_left _ _).trans (le_max_left _ _)
      have hy : y ∈ Set.Icc (f t L) (f t U) := by
        rw [hfix t L hL, hfix t U hU]
        exact ⟨min_le_left _ _, le_max_left _ _⟩
      obtain ⟨x, hx, he⟩ := intermediate_value_Icc hLU
        ((hf.comp (continuous_const.prodMk continuous_id)).continuousOn) hy
      exact ⟨x, he⟩
    have hbound (t : Interval) (x : Set.Ioo (-1 : ℝ) 1) : f t x.val ∈ Set.Ioo (-1 : ℝ) 1 := by
      have hm := hmono t x.property.1
      have hp := hmono t x.property.2
      rw [hfix t (-1) (by simpa using hρ1.le)] at hm
      rw [hfix t 1 (by simpa using hρ1.le)] at hp
      exact ⟨hm, hp⟩
    let width : Interval → Set.Ioo (-1 : ℝ) 1 → Set.Ioo (-1 : ℝ) 1 :=
      fun t x => ⟨f t x.val, hbound t x⟩
    have hwc : Continuous (fun z : Interval × Set.Ioo (-1 : ℝ) 1 => width z.1 z.2) :=
      (hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    have hwmono (t : Interval) : StrictMono (width t) := fun x y hxy => hmono t hxy
    have hwsurj (t : Interval) : Function.Surjective (width t) := by
      intro y
      obtain ⟨x, hx⟩ := hsurj t y.val
      have hxlo : -1 < x := by
        apply (hmono t).lt_iff_lt.mp
        rw [hfix t (-1) (by simpa using hρ1.le), hx]
        exact y.property.1
      have hxhi : x < 1 := by
        apply (hmono t).lt_iff_lt.mp
        rw [hfix t 1 (by simpa using hρ1.le), hx]
        exact y.property.2
      exact ⟨⟨x, hxlo, hxhi⟩, Subtype.ext hx⟩
    let H : AmbientIsotopy (Set.Ioo (-1 : ℝ) 1 × Circle) := {
      map := ⟨fun z => (width z.1 z.2.1, z.2.2),
        (hwc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
          (continuous_snd.comp continuous_snd)⟩
      homeomorphism_at := by
        intro t
        let q := (hwmono t).orderIsoOfRightInverse (width t)
          (fun y => Classical.choose (hwsurj t y)) (fun y => Classical.choose_spec (hwsurj t y))
        refine ⟨q.toHomeomorph.prodCongr (Homeomorph.refl Circle), fun z => rfl⟩
      at_zero := by
        intro z
        apply Prod.ext
        · apply Subtype.ext
          simp [width, f]
        · rfl }
    refine ⟨H, ?_, ?_⟩
    · intro w
      apply Prod.ext
      · apply Subtype.ext
        change f ⟨1, by norm_num⟩ 0 = a
        simp [f, bump, max_eq_left hρ.le, ne_of_gt hρ]
      · rfl
    · intro t z hz
      apply Prod.ext
      · apply Subtype.ext
        exact hfix t z.1.val hz
      · rfl
  have hcompactCollarGeometry
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
      ∃ (B V : Set S) (cminus cplus : Curve S),
        IsCompact B ∧ IsOpen V ∧ V ⊆ B ∧
        Set.range (fun w : Circle => E (⟨0, by norm_num⟩, w)) ⊆ V ∧
        frontier V ⊆ cminus.image ∪ cplus.image ∧
        Disjoint cminus.image cplus.image ∧
        B = E '' {z | |(z.1 : ℝ)| ≤ δ} ∧
        V = E '' {z | |(z.1 : ℝ)| < δ} ∧
        cminus.map = (fun w => E (⟨-δ, by constructor <;> linarith⟩, w)) ∧
        cplus.map = (fun w => E (⟨δ, by constructor <;> linarith⟩, w)) := by
    let tm : Set.Ioo (-1 : ℝ) 1 := ⟨-δ, by constructor <;> linarith⟩
    let tp : Set.Ioo (-1 : ℝ) 1 := ⟨δ, by constructor <;> linarith⟩
    let cm : Curve S := ⟨fun w => E (tm, w), hE.isEmbedding.comp (isEmbedding_prodMkRight tm)⟩
    let cp : Curve S := ⟨fun w => E (tp, w), hE.isEmbedding.comp (isEmbedding_prodMkRight tp)⟩
    let K : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := {z | |(z.1 : ℝ)| ≤ δ}
    let W : Set (Set.Ioo (-1 : ℝ) 1 × Circle) := {z | |(z.1 : ℝ)| < δ}
    let f : Set.Icc (-δ) δ → Set.Ioo (-1 : ℝ) 1 := fun t =>
      ⟨t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    have hK : IsCompact K := by
      have heq : K = (f '' Set.univ) ×ˢ (Set.univ : Set Circle) := by
        ext z
        constructor
        · intro hz
          refine ⟨⟨⟨z.1.val, abs_le.mp hz⟩, Set.mem_univ _, ?_⟩, Set.mem_univ _⟩
          exact Subtype.ext rfl
        · rintro ⟨⟨t, ht, he⟩, hw⟩
          have hv : t.val = z.1.val := congrArg Subtype.val he
          exact abs_le.mpr (hv ▸ t.property)
      rw [heq]
      exact (isCompact_univ.image hf).prod isCompact_univ
    have hW : IsOpen W := isOpen_Iio.preimage
      (continuous_abs.comp (continuous_subtype_val.comp continuous_fst))
    have hB : IsCompact (E '' K) := hK.image E.continuous
    have hV : IsOpen (E '' W) := hE.isOpenMap W hW
    have hVB : E '' W ⊆ E '' K := Set.image_mono (by
      intro z hz
      change |(z.1 : ℝ)| ≤ δ
      change |(z.1 : ℝ)| < δ at hz
      exact hz.le)
    refine ⟨E '' K, E '' W, cm, cp, hB, hV, hVB, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · rintro y ⟨w, rfl⟩
      exact ⟨(⟨0, by norm_num⟩, w), by simpa [W] using hδ, rfl⟩
    · intro y hy
      have hyB : y ∈ E '' K :=
        (closure_minimal hVB hB.isClosed) hy.1
      obtain ⟨⟨t, w⟩, ht, rfl⟩ := hyB
      have hn : ¬ |(t : ℝ)| < δ := by
        intro hh
        apply hy.2
        rw [hV.interior_eq]
        exact ⟨(t,w), hh, rfl⟩
      have habs : |(t : ℝ)| = δ := le_antisymm ht (not_lt.mp hn)
      rcases (abs_eq hδ.le).mp habs with hp | hm
      · right
        exact ⟨w, congrArg (fun u => E (u,w)) (Subtype.ext hp).symm⟩
      · left
        exact ⟨w, congrArg (fun u => E (u,w)) (Subtype.ext hm).symm⟩
    · apply Set.disjoint_left.mpr
      rintro y ⟨u, hu⟩ ⟨w, hw⟩
      have he := hE.injective (hu.trans hw.symm)
      have ht := congrArg (fun z : Set.Ioo (-1 : ℝ) 1 × Circle => (z.1 : ℝ)) he
      change -δ = δ at ht
      linarith
  have hopenSupported (U : Set S) (hUopen : IsOpen U) (H : AmbientIsotopy ↥U) (K : Set S)
      (hK : IsCompact K) (hKP : K ⊆ U)
      (hfix : ∀ t (y : ↥U), y.val ∉ K → H.map (t, y) = y) :
      ∃ G : AmbientIsotopy S,
        (∀ t (y : ↥U), G.map (t, y.val) = (H.map (t, y)).val) ∧
        (∀ t y, y ∉ U → G.map (t, y) = y) := by
    let F : Interval × S → S := fun z =>
      if hz : z.2 ∈ U then (H.map (z.1, ⟨z.2, hz⟩)).val else z.2
    have hFin (t : Interval) (y : ↥U) : F (t, y.val) = (H.map (t, y)).val := by
      dsimp [F]
      rw [dif_pos y.property]
    have hFout (t : Interval) (y : S) (hy : y ∉ K) : F (t, y) = y := by
      dsimp [F]
      split_ifs with hyP
      · exact congrArg Subtype.val (hfix t ⟨y, hyP⟩ hy)
      · rfl
    let A : Set (Interval × S) := {z | z.2 ∈ U}
    let B : Set (Interval × S) := {z | z.2 ∉ K}
    have hAo : IsOpen A := hUopen.preimage continuous_snd
    have hBo : IsOpen B := hK.isClosed.isOpen_compl.preimage continuous_snd
    have hcover : A ∪ B = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      by_cases hz : z.2 ∈ K
      · exact Or.inl (hKP hz)
      · exact Or.inr hz
    have hcontA : ContinuousOn F A := by
      rw [continuousOn_iff_continuous_restrict]
      let k : A → Interval × ↥U := fun z => (z.val.1, ⟨z.val.2, z.property⟩)
      have hk : Continuous k :=
        (continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
      have heq : (fun z : A => F z.val) = fun z => (H.map (k z)).val := by
        funext z
        exact hFin z.val.1 ⟨z.val.2, z.property⟩
      change Continuous (fun z : A => F z.val)
      rw [heq]
      exact continuous_subtype_val.comp (H.map.continuous.comp hk)
    have hcontB : ContinuousOn F B :=
      continuous_snd.continuousOn.congr (fun z hz => hFout z.1 z.2 hz)
    have hcont : Continuous F := by
      rw [← continuousOn_univ, ← hcover]
      exact hcontA.union_of_isOpen hcontB hAo hBo
    have hhomeo (t : Interval) : ∃ e : S ≃ₜ S, ∀ y, e y = F (t, y) := by
      obtain ⟨e, he⟩ := H.homeomorphism_at t
      have hi : Function.Injective (fun y => F (t, y)) := by
        intro y z hyz
        change F (t, y) = F (t, z) at hyz
        by_cases hy : y ∈ U
        · by_cases hz : z ∈ U
          · have h := hyz
            rw [hFin t ⟨y, hy⟩, hFin t ⟨z, hz⟩] at h
            have hh : e ⟨y, hy⟩ = e ⟨z, hz⟩ :=
              (he _).trans ((Subtype.ext h).trans (he _).symm)
            exact congrArg Subtype.val (e.injective hh)
          · have h := hyz
            rw [hFin t ⟨y, hy⟩] at h
            have hzout : F (t, z) = z := by simp only [F, dif_neg hz]
            rw [hzout] at h
            exact False.elim (hz (h ▸ (H.map (t, ⟨y, hy⟩)).property))
        · by_cases hz : z ∈ U
          · have h := hyz
            rw [hFin t ⟨z, hz⟩] at h
            have hyout : F (t, y) = y := by simp only [F, dif_neg hy]
            rw [hyout] at h
            exact False.elim (hy (h.symm ▸ (H.map (t, ⟨z, hz⟩)).property))
          · simpa only [F, dif_neg hy, dif_neg hz] using hyz
      have hs : Function.Surjective (fun y => F (t, y)) := by
        intro y
        by_cases hy : y ∈ U
        · refine ⟨(e.symm ⟨y, hy⟩).val, ?_⟩
          change F (t, (e.symm ⟨y, hy⟩).val) = y
          rw [hFin, ← he, e.apply_symm_apply]
        · refine ⟨y, ?_⟩
          simp only [F, dif_neg hy]
      let eS := (hcont.comp (continuous_const.prodMk continuous_id)).homeoOfEquivCompactToT2
        (f := Equiv.ofBijective (fun y => F (t, y)) ⟨hi, hs⟩)
      exact ⟨eS, fun _ => rfl⟩
    let G : AmbientIsotopy S := {
      map := ⟨F, hcont⟩
      homeomorphism_at := hhomeo
      at_zero := by
        intro y
        change F (⟨0, by norm_num⟩, y) = y
        by_cases hy : y ∈ U
        · rw [hFin _ ⟨y, hy⟩]
          exact congrArg Subtype.val (H.at_zero ⟨y, hy⟩)
        · simp only [F, dif_neg hy] }
    refine ⟨G, hFin, ?_⟩
    intro t y hy
    have hyn : y ∉ U := hy
    change F (t, y) = y
    simp only [F, dif_neg hyn]
  have hslideCollar
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
      (a : Set.Ioo (-1 : ℝ) 1) (ha : |(a : ℝ)| < ρ) :
      AmbientIsotopy.Rel
        (Set.range (fun w : Circle => E (⟨0, by norm_num⟩, w)))
        (Set.range (fun w : Circle => E (a, w))) := by
    obtain ⟨H, hHcore, hHfix⟩ := hwidthSlide ρ a.val hρ hρ1 ha
    obtain ⟨K, V, cm, cp, hK, hV, hVK, hcenter, hfront, hdist, hKdef, hVdef, hmmap, hpmap⟩ :=
      hcompactCollarGeometry E hE ρ hρ hρ1
    let q := hE.isEmbedding.toHomeomorph
    let J : AmbientIsotopy ↥(Set.range E) := {
      map := ⟨fun z => q (H.map (z.1, q.symm z.2)),
        q.continuous.comp (H.map.continuous.comp
          (continuous_fst.prodMk (q.symm.continuous.comp continuous_snd)))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨h, hh⟩ := H.homeomorphism_at t
        exact ⟨(q.symm.trans h).trans q, fun y => congrArg q (hh (q.symm y))⟩
      at_zero := by
        intro y
        change q (H.map (⟨0, by norm_num⟩, q.symm y)) = y
        rw [H.at_zero, q.apply_symm_apply] }
    have hKrange : K ⊆ Set.range E := by
      rw [hKdef]
      exact Set.image_subset_range _ _
    have hJfix : ∀ t (y : ↥(Set.range E)), y.val ∉ K → J.map (t, y) = y := by
      intro t y hy
      have hn : ¬ |((q.symm y).1 : ℝ)| ≤ ρ := by
        intro hle
        apply hy
        rw [hKdef]
        refine ⟨q.symm y, hle, ?_⟩
        exact congrArg Subtype.val (q.apply_symm_apply y)
      change q (H.map (t, q.symm y)) = y
      rw [hHfix t (q.symm y) (not_le.mp hn).le, q.apply_symm_apply]
    obtain ⟨G, hG, hout⟩ := hopenSupported (Set.range E) hE.isOpen_range J K hK hKrange hJfix
    have hGcore (w : Circle) : G.finalMap (E (⟨0, by norm_num⟩, w)) = E (a, w) := by
      let z : Set.Ioo (-1 : ℝ) 1 × Circle := (⟨0, by norm_num⟩, w)
      have hh := hG ⟨1, by norm_num⟩ (q z)
      change G.finalMap (E z) = E (H.finalMap (q.symm (q z))) at hh
      rw [q.symm_apply_apply, hHcore] at hh
      exact hh
    refine ⟨G, ?_⟩
    ext y
    constructor
    · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (hGcore w).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨E (⟨0, by norm_num⟩, w), ⟨w, rfl⟩, hGcore w⟩
  have hoffsetEssential (b : EssentialCurve S)
      (E : C(Set.Ioo (-1 : ℝ) 1 × Circle, S)) (hE : Topology.IsOpenEmbedding E)
      (hcore : ∀ w, E (⟨0, by norm_num⟩, w) = b.val.map w)
      (t : Set.Ioo (-1 : ℝ) 1) :
      ∃ c : EssentialCurve S, c.val.map = (fun w => E (t,w)) ∧
        Quotient.mk (essentialCurveSetoid S) c = Quotient.mk (essentialCurveSetoid S) b := by
    have ht : |(t : ℝ)| < 1 := abs_lt.mpr t.property
    let ρ : ℝ := (|(t : ℝ)| + 1) / 2
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
    have htρ : |(t : ℝ)| < ρ := by dsimp [ρ]; linarith
    have hrel := hslideCollar E hE ρ hρ hρ1 t htρ
    let c : Curve S := ⟨fun w => E (t,w), hE.isEmbedding.comp (isEmbedding_prodMkRight t)⟩
    have hc : Set.range (fun w : Circle => E (⟨0, by norm_num⟩, w)) = b.val.image := by
      have he : (fun w : Circle => E (⟨0, by norm_num⟩, w)) = b.val.map := funext hcore
      rw [he]
      rfl
    rw [hc] at hrel
    have hrel' : AmbientIsotopy.Rel b.val.image c.image := hrel
    let ce : EssentialCurve S := ⟨c, (essential_isotopy_invariant hrel').mp b.property⟩
    exact ⟨ce, rfl, (Quotient.sound hrel').symm⟩
  have hActualRegionInteriorEssentialCircle (j : J) :
      ∃ b : EssentialCurve S,b.val.image ⊆ interior F ∧
        Quotient.mk (essentialCurveSetoid S) b=Quotient.mk (essentialCurveSetoid S) (c j) := by
    obtain ⟨E,δ,hE,hcore,hδ,hδ1,hside⟩ := hActualRetainedFrontierInteriorCollar j
    rcases hside with hp | hm
    · let t : Set.Ioo (-1 : ℝ) 1 := ⟨δ/2,by constructor <;> linarith⟩
      obtain ⟨b,hb,hclass⟩ := hoffsetEssential (c j) E hE hcore t
      refine ⟨b,?_,hclass⟩
      rintro y ⟨w,rfl⟩
      change b.val.map w∈interior F
      rw [hb]
      exact hp t w (by change 0<δ/2; linarith) (by change δ/2<δ; linarith)
    · let t : Set.Ioo (-1 : ℝ) 1 := ⟨-δ/2,by constructor <;> linarith⟩
      obtain ⟨b,hb,hclass⟩ := hoffsetEssential (c j) E hE hcore t
      refine ⟨b,?_,hclass⟩
      rintro y ⟨w,rfl⟩
      change b.val.map w∈interior F
      rw [hb]
      exact hm t w (by change -δ< -δ/2; linarith) (by change -δ/2<0; linarith)
  have hActualBoundaryEntryArc (S : Type) [TopologicalSpace S] [T2Space S]
      (F : Set S) (hreg : closure (interior F)=F)
      (E : OpenPartialHomeomorph S Schoenflies.Plane) (p : S)
      (hp : p∈E.source) (hEp : E p=0) (hpf : p∈frontier F)
      (r : ℝ) (hr : 0<r) (htarget : Schoenflies.Plane.openSquare 0 r ⊆ E.target)
      (hfront : ∀ y∈E.source,y∈frontier F ↔ E y 1=0) :
      ∃ y : S,∃ a : Path p y,Function.Injective a ∧
        ∀ t : Interval,0<t → a t∈interior F := by
    classical
    let B := Schoenflies.Plane.openSquare 0 r
    have hB : IsOpen B := Schoenflies.Plane.isOpen_openSquare 0 r
    have h0B : (0 : Schoenflies.Plane)∈B := by
      simp [B,Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,hr]
    have hpB : p∈E.symm '' B := ⟨0,h0B,by rw [←hEp,E.left_inv hp]⟩
    have hU : IsOpen (E.symm '' B) := E.symm.isOpen_image_of_subset_source hB htarget
    have hFclosed : IsClosed F := hreg ▸ isClosed_closure
    have hpF : p∈F := hFclosed.frontier_subset hpf
    have hpcl : p∈closure (interior F) := hreg.symm ▸ hpF
    obtain ⟨y,hyB,hyI⟩ := (mem_closure_iff_nhds.mp hpcl) (E.symm '' B) (hU.mem_nhds hpB)
    obtain ⟨v,hvB,hvy⟩ := hyB
    have hv1 : v 1≠0 := by
      intro he
      have hyfront : E.symm v∈frontier F := (hfront _ (E.map_target (htarget hvB))).mpr
        (by rw [E.right_inv (htarget hvB)]; exact he)
      exact Set.disjoint_left.mp disjoint_interior_frontier (hvy.symm ▸ hyI) hyfront
    have hvne : v≠0 := fun he => hv1 (by rw [he]; rfl)
    let f : C(Interval,Schoenflies.Plane) := ⟨fun t => (t:ℝ) • v,by fun_prop⟩
    have hfB : ∀ t,f t∈B := by
      intro t
      have hc := (Schoenflies.Plane.convex_openSquare 0 r) h0B hvB
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring : (1-(t:ℝ))+(t:ℝ)=1)
      simpa [f,smul_zero] using hc
    let a : Path p y := {
      toFun := fun t => E.symm (f t)
      continuous_toFun := E.continuousOn_symm.comp_continuous f.continuous (fun t => htarget (hfB t))
      source' := by change E.symm ((0:ℝ) • v)=p; rw [zero_smul,←hEp,E.left_inv hp]
      target' := by change E.symm ((1:ℝ) • v)=y; simpa using hvy }
    have ha : Function.Injective a := by
      intro t s he
      have he' := E.symm.injOn (htarget (hfB t)) (htarget (hfB s)) he
      have hval := (smul_left_injective ℝ hvne) he'
      exact Subtype.ext hval
    have hposconn : IsPreconnected (a '' Set.Ioc (0 : Interval) 1) :=
      isPreconnected_Ioc.image a a.continuous.continuousOn
    have hposavoid : Disjoint (a '' Set.Ioc (0 : Interval) 1) (frontier F) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨t,ht,rfl⟩ hz
      have he := (hfront _ (E.map_target (htarget (hfB t)))).mp hz
      change E (E.symm (f t)) 1=0 at he
      rw [E.right_inv (htarget (hfB t))] at he
      change (t:ℝ)*v 1=0 at he
      have ht0 : 0<(t:ℝ) := ht.1
      exact hv1 ((mul_eq_zero.mp he).resolve_left (ne_of_gt ht0))
    rcases connected_cap_side F (a '' Set.Ioc (0 : Interval) 1) hposconn hposavoid with hin | hout
    · exact ⟨y,a,ha,fun t ht => hin ⟨t,⟨ht,t.property.2⟩,rfl⟩⟩
    · have hyout : y∈interior Fᶜ := a.target ▸ hout ⟨1,⟨by norm_num,le_rfl⟩,rfl⟩
      exact False.elim ((interior_subset hyout) (interior_subset hyI))
  have hActualGenericBoundaryEmbeddedAccess (y : S) (hy : y∈interior F) :
      ∃ a : C(Interval,↥F),Topology.IsEmbedding a ∧
        (a 0).val∈(chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
        (a 1).val=y ∧ ∀ t : Interval,0<t → (a t).val∈interior F := by
    obtain ⟨b,hb⟩ := hActualChartBoundaryCurve x R hR htarget
    let p : S := b.map 1
    have hpB : p∈b.image := Set.mem_range_self 1
    let K : Set S := ⋃ j,(c j).val.image
    have hK : IsCompact K := isCompact_iUnion (fun j => isCompact_range (c j).val.embedded.continuous)
    have hpK : p∉K := by
      intro hk
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hk
      exact Set.disjoint_left.mp (hbaseDisjoint j) hj (hb ▸ hpB)
    obtain ⟨E,hpE,hEp,hEK,hEt,hEaxis⟩ :=
      CurveComplex.PositionUniverseV2.position_curve_crosscut_chart S b p hpB
        Kᶜ hK.isClosed.isOpen_compl hpK
    have hfrontE : ∀ z∈E.source,z∈frontier F ↔ E z 1=0 := by
      intro z hz
      rw [←hEaxis z hz,hfrontier,←hb]
      exact ⟨fun h => h.resolve_right (hEK hz),Or.inl⟩
    have hpfront : p∈frontier F := by rw [hfrontier,←hb];exact Or.inl hpB
    have ht : Schoenflies.Plane.openSquare 0 (1/2:ℝ) ⊆ E.target := by
      intro z hz
      apply hEt
      change Schoenflies.Plane.supDist z 0≤1
      change Schoenflies.Plane.supDist z 0<1/2 at hz
      linarith
    obtain ⟨z,entry,hentry,hentryI⟩ := hActualBoundaryEntryArc S F hregular E p hpE hEp hpfront
      (1/2) (by norm_num) ht hfrontE
    have hzI : z∈interior F := entry.target ▸ hentryI 1 (by norm_num)
    have hpnotI : p∉interior F := fun hi => Set.disjoint_left.mp disjoint_interior_frontier hi hpfront
    have hpy : p≠y := fun he => hpnotI (he.symm ▸ hy)
    have haccess : ∃ r : Path p y,Function.Injective r ∧
        ∀ t : Interval,0<t → r t∈interior F := by
      by_cases hzy : z=y
      · exact ⟨entry.cast rfl hzy.symm,by simpa only [Path.cast_coe] using hentry,
          by simpa only [Path.cast_coe] using hentryI⟩
      · obtain ⟨q,hq,hqI⟩ := hOpenRegionSimpleArc (interior F) isOpen_interior
          hActualRegionInteriorConnected.isPreconnected z y hzI hy hzy
        obtain ⟨r,hr,hrsub⟩ := hSimpleJoin entry q hentry hq hpy
        refine ⟨r,hr,?_⟩
        intro t ht'
        rcases hrsub (Set.mem_range_self t) with he | hq'
        · obtain ⟨u,hu⟩ := he
          have hu0 : 0<u := by
            apply lt_of_le_of_ne u.property.1
            intro hu0
            have hu' : u=0 := Subtype.ext hu0.symm
            have he0 : r t=r 0 := hu.symm.trans (by rw [hu',entry.source,r.source])
            have ht0 : t=0 := hr he0
            exact (ne_of_gt ht') ht0
          exact hu ▸ hentryI u hu0
        · exact hqI hq'
    obtain ⟨r,hr,hrI⟩ := haccess
    have hrF : ∀ t,r t∈F := by
      intro t
      by_cases ht0 : t=0
      · rw [ht0,r.source];exact hbase (hb ▸ hpB)
      · exact interior_subset (hrI t (lt_of_le_of_ne t.property.1 (Ne.symm ht0)))
    let a : C(Interval,↥F) := ⟨fun t => ⟨r t,hrF t⟩,r.continuous.subtype_mk hrF⟩
    have hai : Function.Injective a := fun t s he => hr (congrArg Subtype.val he)
    refine ⟨a,(a.continuous.isClosedEmbedding hai).isEmbedding,?_,?_,hrI⟩
    · change r 0∈_
      rw [r.source]
      exact hb ▸ hpB
    · exact r.target
  let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
  have hActualBaseInFrontier {y : S} (hy : y∈boundaryCircle) : y∈frontier F := by
    rw [hfrontier]
    exact Or.inl hy
  have hActualGenericEssentialCircleEmbeddedFirstAccess (j : J) :
      ∃ (b : EssentialCurve S) (a : C(Interval,↥F)),
        Topology.IsEmbedding a ∧ b.val.image ⊆ interior F ∧
        Quotient.mk (essentialCurveSetoid S) b = Quotient.mk (essentialCurveSetoid S) (c j) ∧
        (a 0).val ∈ boundaryCircle ∧ (a 1).val ∈ b.val.image ∧
        (∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ b.val.image) ∧
        ∀ t : Interval, 0 < t → (a t).val ∈ interior F := by
    obtain ⟨b,hc,hclass⟩ := hActualRegionInteriorEssentialCircle j
    let u : Circle := 1
    obtain ⟨p,hpemb,hp0,hp1,hpI⟩ :=
      hActualGenericBoundaryEmbeddedAccess (b.val.map u) (hc (Set.mem_range_self u))
    let T : Set Interval := {t | (p t).val ∈ b.val.image}
    have hT : IsCompact T :=
      ((isCompact_range b.val.embedded.continuous).isClosed.preimage
        (continuous_subtype_val.comp p.continuous)).isCompact
    have hTne : T.Nonempty := ⟨1,by change (p 1).val ∈ b.val.image; rw [hp1]; exact Set.mem_range_self u⟩
    obtain ⟨s,hs,hmin⟩ := hT.exists_isLeast hTne
    have hs0 : 0 < s := by
      apply lt_of_le_of_ne s.property.1
      intro he
      have hsZero : s = 0 := Subtype.ext he.symm
      have hpC : (p 0).val ∈ b.val.image := hsZero ▸ hs
      exact Set.disjoint_left.mp disjoint_interior_frontier (hc hpC) (hActualBaseInFrontier hp0)
    let clock : C(Interval,Interval) := {
      toFun := fun t => ⟨(s:ℝ)*(t:ℝ),by
        constructor <;> nlinarith [s.property.1,s.property.2,t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
    have hc0 : clock 0 = 0 := by apply Subtype.ext; change (s:ℝ)*0=0; ring
    have hc1 : clock 1 = s := by apply Subtype.ext; change (s:ℝ)*1=(s:ℝ); ring
    let a : C(Interval,↥F) := p.comp clock
    have hainj : Function.Injective a := by
      intro t v he
      have hv := congrArg Subtype.val (hpemb.injective he)
      change (s:ℝ)*(t:ℝ)=(s:ℝ)*(v:ℝ) at hv
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt (show 0 < (s:ℝ) from hs0)) hv)
    refine ⟨b,a,(a.continuous.isClosedEmbedding hainj).isEmbedding,hc,hclass,?_,?_,?_,?_⟩
    · change (p (clock 0)).val ∈ boundaryCircle
      rw [hc0]
      exact hp0
    · change (p (clock 1)).val ∈ b.val.image
      rw [hc1]
      exact hs
    · intro t ht hh
      have hle : s ≤ clock t := hmin hh
      change (s:ℝ) ≤ (s:ℝ)*(t:ℝ) at hle
      have hspos : 0 < (s:ℝ) := hs0
      have htlt : (t:ℝ) < 1 := ht.2
      nlinarith
    · intro t ht
      apply hpI
      change 0 < (s:ℝ)*(t:ℝ)
      exact mul_pos hs0 ht
  have hActualGenericEssentialCircleEmbeddedCleanAccess (j : J) :
      ∃ (b : EssentialCurve S) (a : C(Interval,↥F)),
        Topology.IsEmbedding a ∧ b.val.image ⊆ interior F ∧
        Quotient.mk (essentialCurveSetoid S) b = Quotient.mk (essentialCurveSetoid S) (c j) ∧
        (a 0).val ∈ boundaryCircle ∧
        (∀ t, (a t).val ∈ b.val.image ↔ t = 1) ∧
        (∀ t, (a t).val ∈ frontier F ↔ t = 0) ∧
        (a 0).val ≠ (a 1).val ∧
        ∀ t : Interval, 0 < t → (a t).val ∈ interior F := by
    obtain ⟨b,a,haemb,hc,hclass,hbase,hend,hfirst,hinside⟩ :=
      hActualGenericEssentialCircleEmbeddedFirstAccess j
    have hc0 : (a 0).val ∉ b.val.image := by
      intro hh
      exact Set.disjoint_left.mp disjoint_interior_frontier (hc hh)
        (hActualBaseInFrontier hbase)
    have hcircle (t : Interval) : (a t).val ∈ b.val.image ↔ t = 1 := by
      constructor
      · intro ht
        by_contra hn
        by_cases ht0 : t = 0
        · exact hc0 (ht0 ▸ ht)
        · exact hfirst t ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
            lt_of_le_of_ne t.property.2 hn⟩ ht
      · rintro rfl
        exact hend
    have hfrontier (t : Interval) :
        (a t).val ∈ frontier F ↔ t = 0 := by
      constructor
      · intro ht
        by_contra hn
        exact Set.disjoint_left.mp disjoint_interior_frontier
          (hinside t (lt_of_le_of_ne t.property.1 (Ne.symm hn))) ht
      · rintro rfl
        exact hActualBaseInFrontier hbase
    refine ⟨b,a,haemb,hc,hclass,hbase,hcircle,hfrontier,?_,hinside⟩
    intro he
    exact hc0 (he.symm ▸ hend)
  have hActualEmbeddedConnectorMiddleStrip (F : Set S)
      (c : EssentialCurve S) (a : C(Interval,↥F))
      (ha : Topology.IsEmbedding a)
      (hcircle : ∀ t, (a t).val ∈ c.val.image ↔ t = 1)
      (hinside : ∀ t : Interval, 0 < t → (a t).val ∈ interior F)
      (l r : Interval) (hl : 0 < l) (hlr : l < r) (hr : r < 1) :
      ∃ N : Interval × Set.Icc (-1 : ℝ) 1 → S,
        Topology.IsEmbedding N ∧
        (∀ t, N (t,⟨0,by norm_num⟩) =
          (a ⟨(l:ℝ)+((r:ℝ)-(l:ℝ))*(t:ℝ),by
            constructor <;> nlinarith [l.property.1,r.property.2,t.property.1,t.property.2, (show (l:ℝ) < r from hlr)]⟩).val) ∧
        Set.range N ⊆ interior F \ c.val.image ∧
        ∀ z, N z ∈ Set.range (fun t => (a t).val) ↔ (z.2:ℝ) = 0 := by
    let f : C(Interval,S) := ⟨fun t => (a t).val,
      continuous_subtype_val.comp a.continuous⟩
    have hf : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp ha
    obtain ⟨E,hE,hcenter,hEU⟩ := CurveComplex.source_whole_embedded_arc_strip
      f hf Set.univ isOpen_univ (Set.subset_univ _)
    let U : Set S := interior F \ c.val.image
    have hU : IsOpen U := isOpen_interior.sdiff
      (isCompact_range c.val.embedded.continuous).isClosed
    let K : Set Interval := Set.Icc l r
    have hK : IsCompact K := isCompact_Icc
    have hprod : K ×ˢ ({⟨0,by norm_num⟩} : Set (Set.Icc (-1 : ℝ) 1)) ⊆ E ⁻¹' U := by
      rintro ⟨t,w⟩ ⟨ht,hw⟩
      have hw0 : w = ⟨0,by norm_num⟩ := hw
      subst w
      change E (t,⟨0,by norm_num⟩) ∈ U
      rw [hcenter]
      refine ⟨hinside t (hl.trans_le ht.1),?_⟩
      intro hc
      have ht1 := (hcircle t).mp hc
      have htlt : t < 1 := ht.2.trans_lt hr
      exact (ne_of_lt htlt) ht1
    obtain ⟨V,W,hV,hW,hKV,hzero,hVW⟩ := generalized_tube_lemma
      hK (isCompact_singleton (x := (⟨0,by norm_num⟩ : Set.Icc (-1 : ℝ) 1)))
      (hU.preimage hE.continuous) hprod
    obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp hW ⟨0,by norm_num⟩ (hzero (Set.mem_singleton _))
    let δ : ℝ := min η 1 / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδη : δ < η := by dsimp [δ]; have hh := min_le_left η 1; linarith
    have hδ1 : δ < 1 := by dsimp [δ]; have hh := min_le_right η 1; linarith
    let clock (t : Interval) : Interval :=
      ⟨(l:ℝ)+((r:ℝ)-(l:ℝ))*(t:ℝ),by
        constructor <;> nlinarith [l.property.1,r.property.2,t.property.1,t.property.2, (show (l:ℝ) < r from hlr)]⟩
    have hclock : Continuous clock := by dsimp [clock]; fun_prop
    have hclockK (t : Interval) : clock t ∈ K := by
      change (l:ℝ) ≤ (l:ℝ)+((r:ℝ)-(l:ℝ))*(t:ℝ) ∧
        (l:ℝ)+((r:ℝ)-(l:ℝ))*(t:ℝ) ≤ (r:ℝ)
      have hlt : (l:ℝ) < r := hlr
      constructor <;> nlinarith [t.property.1,t.property.2]
    let width (w : Set.Icc (-1 : ℝ) 1) : Set.Icc (-1 : ℝ) 1 :=
      ⟨δ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2]⟩
    have hwidth : Continuous width := by dsimp [width]; fun_prop
    have hwidthW (w : Set.Icc (-1 : ℝ) 1) : width w ∈ W := by
      apply hball
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,sub_zero,abs_lt]
      change -η < δ*(w:ℝ) ∧ δ*(w:ℝ) < η
      constructor <;> nlinarith [w.property.1,w.property.2]
    let N : Interval × Set.Icc (-1 : ℝ) 1 → S := fun z => E (clock z.1,width z.2)
    have hNc : Continuous N := hE.continuous.comp
      ((hclock.comp continuous_fst).prodMk (hwidth.comp continuous_snd))
    have hNi : Function.Injective N := by
      intro z w he
      have hv := hE.injective he
      apply Prod.ext
      · apply Subtype.ext
        have hh := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.1:ℝ)) hv
        change (l:ℝ)+((r:ℝ)-(l:ℝ))*(z.1:ℝ) =
          (l:ℝ)+((r:ℝ)-(l:ℝ))*(w.1:ℝ) at hh
        have hlt : (l:ℝ) < r := hlr
        nlinarith
      · apply Subtype.ext
        have hh := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2:ℝ)) hv
        change δ*(z.2:ℝ)=δ*(w.2:ℝ) at hh
        exact mul_left_cancel₀ (ne_of_gt hδ) hh
    refine ⟨N,(hNc.isClosedEmbedding hNi).isEmbedding,?_,?_,?_⟩
    · intro t
      have hz : width ⟨0,by norm_num⟩ = ⟨0,by norm_num⟩ :=
        Subtype.ext (by change δ*0=0; ring)
      change E (clock t,width ⟨0,by norm_num⟩) = f (clock t)
      rw [hz,hcenter]
    · rintro y ⟨z,rfl⟩
      exact hVW ⟨hKV (hclockK z.1),hwidthW z.2⟩
    · intro z
      constructor
      · rintro ⟨t,ht⟩
        have hh : E (clock z.1,width z.2) = E (t,⟨0,by norm_num⟩) := by
          rw [hcenter]
          exact ht.symm
        have hw := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2:ℝ)) (hE.injective hh)
        change δ*(z.2:ℝ)=0 at hw
        exact (mul_eq_zero.mp hw).resolve_left (ne_of_gt hδ)
      · intro hz
        have hw : width z.2 = ⟨0,by norm_num⟩ := Subtype.ext (by change δ*(z.2:ℝ)=0; rw [hz,mul_zero])
        refine ⟨clock z.1,?_⟩
        change f (clock z.1) = E (clock z.1,width z.2)
        rw [hw,hcenter]
  have hActualTerminalConnectorStarFullTrace (F : Set S)
      (c : EssentialCurve S) (a : C(Interval,↥(F)))
      (ha : Topology.IsEmbedding a) (hc : c.val.image ⊆ interior (F))
      (hcircle : ∀ t, (a t).val ∈ c.val.image ↔ t = 1)
      (hinside : ∀ t : Interval, 0 < t → (a t).val ∈ interior (F)) :
      ∃ (γ : Fin 3 → C(Interval,S)) (K : Set S),
        IsCompact K ∧ (a 1).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ c.val.image) ⊆ K ∪ (⋃ j, Set.range (γ j)) ∧
        (∀ j, Topology.IsEmbedding (γ j)) ∧
        (∀ j, γ j 0 = (a 1).val) ∧
        (∀ j, Set.range (γ j) ⊆ interior (F)) ∧
        Set.range (γ 0) ⊆ Set.range (fun t => (a t).val) ∧
        (∀ j, j ≠ 0 → Set.range (γ j) ⊆ c.val.image) ∧
        ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {(a 1).val} := by
    obtain ⟨u,hu⟩ := (hcircle 1).mpr rfl
    let v : Circle := -u
    have hvu : v ≠ u := Circle.neg_ne_self u
    have hxy : (a 1).val ≠ c.val.map v := by
      intro he
      have huv : u = v := c.val.embedded.injective (hu.trans he)
      exact hvu huv.symm
    obtain ⟨p,q,hp,hq,hp0,hq0,hp1,hq1,hcover,hmeet⟩ :=
      CurveComplex.source_curve_complementary_arcs c.val (a 1).val (c.val.map v)
        ((hcircle 1).mpr rfl) (Set.mem_range_self v) hxy
    let half : C(Interval,Interval) := {
      toFun := fun t => ⟨(t:ℝ)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
    have hhalf : Topology.IsEmbedding half := by
      apply (half.continuous.isClosedEmbedding ?_).isEmbedding
      intro t s he
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      change (t:ℝ)/2=(s:ℝ)/2 at hv
      linarith
    have hh0 : half 0 = 0 := Subtype.ext (by change (0:ℝ)/2=0; ring)
    let back : C(Interval,Interval) := {
      toFun := fun t => ⟨1-(t:ℝ)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
    have hback : Topology.IsEmbedding back := by
      apply (back.continuous.isClosedEmbedding ?_).isEmbedding
      intro t s he
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      change 1-(t:ℝ)/2=1-(s:ℝ)/2 at hv
      linarith
    have hb0 : back 0 = 1 := Subtype.ext (by change 1-(0:ℝ)/2=1; ring)
    let f : C(Interval,S) := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
    let A := f.comp back
    let P := p.comp half
    let Q := q.comp half
    have hA : Topology.IsEmbedding A := (Topology.IsEmbedding.subtypeVal.comp ha).comp hback
    have hP : Topology.IsEmbedding P := hp.comp hhalf
    have hQ : Topology.IsEmbedding Q := hq.comp hhalf
    have hA0 : A 0 = (a 1).val := by change f (back 0) = (a 1).val; rw [hb0]; rfl
    have hP0 : P 0 = (a 1).val := by change p (half 0) = (a 1).val; rw [hh0,hp0]
    have hQ0 : Q 0 = (a 1).val := by change q (half 0) = (a 1).val; rw [hh0,hq0]
    have hAsub : Set.range A ⊆ Set.range (fun t => (a t).val) := by
      rintro y ⟨t,rfl⟩
      exact ⟨back t,rfl⟩
    have hPsub : Set.range P ⊆ c.val.image := by
      rintro y ⟨t,rfl⟩
      rw [← hcover]
      exact Or.inl ⟨half t,rfl⟩
    have hQsub : Set.range Q ⊆ c.val.image := by
      rintro y ⟨t,rfl⟩
      rw [← hcover]
      exact Or.inr ⟨half t,rfl⟩
    have hAPre : Set.range A ∩ c.val.image = {(a 1).val} := by
      ext y
      constructor
      · rintro ⟨⟨t,rfl⟩,hcA⟩
        have ht := (hcircle (back t)).mp hcA
        have hv := congrArg Subtype.val ht
        change 1-(t:ℝ)/2=1 at hv
        have ht0 : t = 0 := Subtype.ext (by change (t:ℝ)=0; linarith)
        simpa only [ht0,hA0,Set.mem_singleton_iff]
      · rintro rfl
        exact ⟨⟨0,hA0⟩,(hcircle 1).mpr rfl⟩
    have hAP : Set.range A ∩ Set.range P = {(a 1).val} := by
      apply Set.Subset.antisymm
      · exact (Set.inter_subset_inter_right _ hPsub).trans hAPre.subset
      · rintro y rfl
        exact ⟨⟨0,hA0⟩,⟨0,hP0⟩⟩
    have hAQ : Set.range A ∩ Set.range Q = {(a 1).val} := by
      apply Set.Subset.antisymm
      · exact (Set.inter_subset_inter_right _ hQsub).trans hAPre.subset
      · rintro y rfl
        exact ⟨⟨0,hA0⟩,⟨0,hQ0⟩⟩
    have hPQ : Set.range P ∩ Set.range Q = {(a 1).val} := by
      ext y
      constructor
      · rintro ⟨⟨t,ht⟩,⟨s,hs⟩⟩
        have hym : y ∈ ({(a 1).val,c.val.map v} : Set S) := by
          rw [← hmeet]
          exact ⟨⟨half t,ht⟩,⟨half s,hs⟩⟩
        rcases hym with hx | hy
        · exact hx
        · have hy' : y = c.val.map v := hy
          have he : p (half t) = p 1 := ht.trans (hy'.trans hp1.symm)
          have hv := congrArg Subtype.val (hp.injective he)
          change (t:ℝ)/2=1 at hv
          exact False.elim (by linarith [t.property.2])
      · rintro rfl
        exact ⟨⟨0,hP0⟩,⟨0,hQ0⟩⟩
    let γ : Fin 3 → C(Interval,S) := ![A,P,Q]
    let l : Interval := ⟨1/4,by constructor <;> norm_num⟩
    let r : Interval := ⟨3/4,by constructor <;> norm_num⟩
    let K : Set S := (f '' Set.Icc 0 r) ∪
      ((p '' Set.Icc l 1) ∪ (q '' Set.Icc l 1))
    have hK : IsCompact K :=
      (isCompact_Icc.image f.continuous).union
        ((isCompact_Icc.image p.continuous).union (isCompact_Icc.image q.continuous))
    have hpK : (a 1).val ∉ K := by
      rintro (hf | hpq)
      · obtain ⟨t,ht,he⟩ := hf
        have ht1 : t = 1 := (Topology.IsEmbedding.subtypeVal.comp ha).injective he
        have hh := ht.2
        rw [ht1] at hh
        change (1:ℝ) ≤ 3/4 at hh
        norm_num at hh
      · rcases hpq with hp' | hq'
        · obtain ⟨t,ht,he⟩ := hp'
          have ht0 : t = 0 := hp.injective (he.trans hp0.symm)
          have hh := ht.1
          rw [ht0] at hh
          change (1/4:ℝ) ≤ 0 at hh
          norm_num at hh
        · obtain ⟨t,ht,he⟩ := hq'
          have ht0 : t = 0 := hq.injective (he.trans hq0.symm)
          have hh := ht.1
          rw [ht0] at hh
          change (1/4:ℝ) ≤ 0 at hh
          norm_num at hh
    have hcoverFull : (Set.range (fun t => (a t).val) ∪ c.val.image) ⊆
        K ∪ (⋃ j, Set.range (γ j)) := by
      intro y hy
      rcases hy with hf | hc'
      · obtain ⟨t,rfl⟩ := hf
        by_cases ht : t ≤ r
        · exact Or.inl (Or.inl ⟨t,⟨t.property.1,ht⟩,rfl⟩)
        · right
          apply Set.mem_iUnion.mpr
          refine ⟨0,?_⟩
          have htr : (3/4:ℝ) < (t:ℝ) := by
            change ¬ (t:ℝ) ≤ 3/4 at ht
            exact lt_of_not_ge ht
          let s : Interval := ⟨2*(1-(t:ℝ)),by constructor <;>
            nlinarith [t.property.1,t.property.2]⟩
          refine ⟨s,?_⟩
          change f (back s) = f t
          congr 1
          apply Subtype.ext
          change 1-(2*(1-(t:ℝ)))/2=(t:ℝ)
          ring
      · rw [← hcover] at hc'
        rcases hc' with hp' | hq'
        · obtain ⟨t,rfl⟩ := hp'
          by_cases ht : l ≤ t
          · exact Or.inl (Or.inr (Or.inl ⟨t,⟨ht,t.property.2⟩,rfl⟩))
          · right
            apply Set.mem_iUnion.mpr
            refine ⟨1,?_⟩
            have htl : (t:ℝ) < (1/4:ℝ) := by
              change ¬ (1/4:ℝ) ≤ (t:ℝ) at ht
              exact lt_of_not_ge ht
            let s : Interval := ⟨2*(t:ℝ),by constructor <;>
              nlinarith [t.property.1,t.property.2]⟩
            refine ⟨s,?_⟩
            change p (half s) = p t
            congr 1
            apply Subtype.ext
            change (2*(t:ℝ))/2=(t:ℝ)
            ring
        · obtain ⟨t,rfl⟩ := hq'
          by_cases ht : l ≤ t
          · exact Or.inl (Or.inr (Or.inr ⟨t,⟨ht,t.property.2⟩,rfl⟩))
          · right
            apply Set.mem_iUnion.mpr
            refine ⟨2,?_⟩
            have htl : (t:ℝ) < (1/4:ℝ) := by
              change ¬ (1/4:ℝ) ≤ (t:ℝ) at ht
              exact lt_of_not_ge ht
            let s : Interval := ⟨2*(t:ℝ),by constructor <;>
              nlinarith [t.property.1,t.property.2]⟩
            refine ⟨s,?_⟩
            change q (half s) = q t
            congr 1
            apply Subtype.ext
            change (2*(t:ℝ))/2=(t:ℝ)
            ring
    refine ⟨γ,K,hK,hpK,hcoverFull,?_,?_,?_,?_,?_,?_⟩
    · intro j
      fin_cases j <;> assumption
    · intro j
      fin_cases j <;> assumption
    · intro j
      fin_cases j
      · rintro y ⟨t,rfl⟩
        exact hinside (back t) (by change 0 < 1-(t:ℝ)/2; linarith [t.property.2])
      · exact hPsub.trans hc
      · exact hQsub.trans hc
    · exact hAsub
    · intro j hj
      fin_cases j
      · exact False.elim (hj rfl)
      · exact hPsub
      · exact hQsub
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact hAP
      · exact hAQ
      · exact (Set.inter_comm (Set.range P) (Set.range A)).trans hAP
      · exact False.elim (hij rfl)
      · exact hPQ
      · exact (Set.inter_comm (Set.range Q) (Set.range A)).trans hAQ
      · exact (Set.inter_comm (Set.range Q) (Set.range P)).trans hPQ
      · exact False.elim (hij rfl)
  have hActualFiniteStarInOneChartClocked (F : Set S)
      (γ : Fin 3 → C(Interval,S)) (p : S)
      (hγ : ∀ j, Topology.IsEmbedding (γ j))
      (hstart : ∀ j, γ j 0 = p)
      (hinside : ∀ j, Set.range (γ j) ⊆ interior (F))
      (hmeet : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {p}) :
      ∃ (β : Fin 3 → C(Interval,S)) (d : Interval),
        0 < d ∧ d < 1 ∧
        (∀ j t, β j t = γ j ⟨(d:ℝ)*(t:ℝ),by constructor <;> nlinarith [d.property.1,d.property.2,t.property.1,t.property.2]⟩) ∧
        (∀ j, Topology.IsEmbedding (β j)) ∧
        (∀ j, β j 0 = p) ∧
        (∀ j, Set.range (β j) ⊆ Set.range (γ j)) ∧
        (∀ j, Set.range (β j) ⊆ interior (F) ∩
          (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) ∧
        ∀ i j, i ≠ j → Set.range (β i) ∩ Set.range (β j) = {p} := by
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
    let W : Set Interval := ⋂ j, γ j ⁻¹' e.source
    have hW : IsOpen W := isOpen_iInter_of_finite (fun j => e.open_source.preimage (γ j).continuous)
    have h0 : (0 : Interval) ∈ W := by
      apply Set.mem_iInter.mpr
      intro j
      change γ j 0 ∈ e.source
      rw [hstart]
      exact ChartedSpace.mem_chart_source p
    obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp hW 0 h0
    let δ : ℝ := min η 1 / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδη : δ < η := by dsimp [δ]; have hh := min_le_left η 1; linarith
    have hδ1 : δ < 1 := by dsimp [δ]; have hh := min_le_right η 1; linarith
    let ρ : C(Interval,Interval) := {
      toFun := fun t => ⟨δ*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
    have hρ : Topology.IsEmbedding ρ := by
      apply (ρ.continuous.isClosedEmbedding ?_).isEmbedding
      intro t s he
      apply Subtype.ext
      exact mul_left_cancel₀ (ne_of_gt hδ) (congrArg Subtype.val he)
    have hρ0 : ρ 0 = 0 := Subtype.ext (by change δ*0=0; ring)
    have hρW (t : Interval) : ρ t ∈ W := by
      apply hball
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
      change |δ*(t:ℝ)-0| < η
      rw [sub_zero,abs_of_nonneg (mul_nonneg hδ.le t.property.1)]
      nlinarith [t.property.2]
    let β : Fin 3 → C(Interval,S) := fun j => (γ j).comp ρ
    have hβsub (j : Fin 3) : Set.range (β j) ⊆ Set.range (γ j) := by
      rintro y ⟨t,rfl⟩
      exact ⟨ρ t,rfl⟩
    have hβ0 (j : Fin 3) : β j 0 = p := by change γ j (ρ 0) = p; rw [hρ0,hstart]
    refine ⟨β,⟨δ,⟨hδ.le,hδ1.le⟩⟩,hδ,hδ1,fun j t => rfl,fun j => (hγ j).comp hρ,hβ0,hβsub,?_,?_⟩
    · intro j
      rintro y ⟨t,rfl⟩
      exact ⟨hinside j (Set.mem_range_self (ρ t)),Set.mem_iInter.mp (hρW t) j⟩
    · intro i j hij
      apply Set.Subset.antisymm
      · exact (Set.inter_subset_inter (hβsub i) (hβsub j)).trans (hmeet i j hij).subset
      · rintro y rfl
        exact ⟨⟨0,hβ0 i⟩,⟨0,hβ0 j⟩⟩
  have hActualTerminalStarRadializationClearance (F : Set S)
      (β : Fin 3 → C(Interval,S)) (p : S)
      (hβ : ∀ j, Topology.IsEmbedding (β j))
      (hstart : ∀ j, β j 0 = p)
      (hinside : ∀ j, Set.range (β j) ⊆ interior F ∩
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
      (hmeet : ∀ i j, i ≠ j → Set.range (β i) ∩ Set.range (β j) = {p})
      (K : Set S) (hK : IsCompact K) (hpK : p ∉ K) :
      ∃ G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2)),
        (∀ j t, G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) p) (β j t) -
          (chartAt (EuclideanSpace ℝ (Fin 2)) p) p) ∧
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
          {z | (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
            (z + (chartAt (EuclideanSpace ℝ (Fin 2)) p) p) ∈ interior F \ K ∧
            z + (chartAt (EuclideanSpace ℝ (Fin 2)) p) p ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) p).target},
          R.vector 2 = -R.vector 1 := by
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
    have hp : p ∈ interior F := by
      have hh := (hinside 0 (Set.mem_range_self 0)).1
      rwa [hstart] at hh
    let G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2)) := fun j => {
      toFun := fun t => e (β j t) - e p
      continuous_toFun :=
        (e.continuousOn.comp_continuous (β j).continuous
          (fun t => (hinside j (Set.mem_range_self t)).2)).sub continuous_const }
    have hGi (j : Fin 3) : Function.Injective (G j) := by
      intro t s he
      apply (hβ j).injective
      apply e.injOn (hinside j (Set.mem_range_self t)).2 (hinside j (Set.mem_range_self s)).2
      exact sub_left_inj.mp he
    have hG0 (j : Fin 3) : G j 0 = 0 := by change e (β j 0) - e p = 0; rw [hstart,sub_self]
    have hGmeet (i j : Fin 3) (hij : i ≠ j) :
        Set.range (G i) ∩ Set.range (G j) = {0} := by
      ext y
      constructor
      · rintro ⟨⟨t,ht⟩,⟨s,hs⟩⟩
        have he : e (β i t) = e (β j s) := sub_left_inj.mp (ht.trans hs.symm)
        have hb : β i t = β j s := e.injOn (hinside i (Set.mem_range_self t)).2
          (hinside j (Set.mem_range_self s)).2 he
        have hm : β i t ∈ ({p} : Set S) := by
          rw [← hmeet i j hij]
          exact ⟨Set.mem_range_self t,⟨s,hb.symm⟩⟩
        have hbp : β i t = p := hm
        have hz : G i t = 0 := by change e (β i t)-e p=0; rw [hbp,sub_self]
        exact Set.mem_singleton_iff.mpr (ht.symm.trans hz)
      · rintro rfl
        exact ⟨⟨0,hG0 i⟩,⟨0,hG0 j⟩⟩
    let V : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | e.symm (z+e p) ∈ interior F \ K ∧ z+e p ∈ e.target}
    have hV : IsOpen V := by
      have hB : IsOpen (e.target ∩ e.symm ⁻¹' (interior F \ K)) :=
        e.isOpen_inter_preimage_symm (isOpen_interior.inter hK.isClosed.isOpen_compl)
      have hadd : Continuous (fun z : EuclideanSpace ℝ (Fin 2) => z + e p) :=
        continuous_id.add continuous_const
      have hh := hB.preimage hadd
      convert hh using 1
      ext z
      exact and_comm
    have h0V : (0 : EuclideanSpace ℝ (Fin 2)) ∈ V := by
      have hps : p ∈ e.source := ChartedSpace.mem_chart_source p
      refine ⟨?_,?_⟩
      · change e.symm (0+e p) ∈ interior F \ K
        rw [zero_add,e.left_inv hps]
        exact ⟨hp,hpK⟩
      · simpa only [zero_add] using e.map_source hps
    obtain ⟨R,hR⟩ := prescribed_pair_finite_actual_star_radialization_zero
      (fun j => G j) (fun j => (G j).continuous.isClosedEmbedding (hGi j))
      hG0 hGmeet (1 : Fin 3) (2 : Fin 3) (by decide) V hV h0V
    exact ⟨G,fun j t => rfl,R,hR⟩
  have hActualTerminalFullTraceRadialization (F : Set S)
      (c : EssentialCurve S) (a : C(Interval,↥F))
      (ha : Topology.IsEmbedding a) (hc : c.val.image ⊆ interior F)
      (hcircle : ∀ t, (a t).val ∈ c.val.image ↔ t = 1)
      (hinside : ∀ t : Interval, 0 < t → (a t).val ∈ interior F) :
      ∃ (K : Set S) (β : Fin 3 → C(Interval,S))
        (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2))),
        IsCompact K ∧ (a 1).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ c.val.image) ⊆ K ∪ (⋃ j,Set.range (β j)) ∧
        (∀ j,Topology.IsEmbedding (β j)) ∧
        (∀ j,Set.range (β j) ⊆ Set.range (fun t => (a t).val) ∪ c.val.image) ∧
        (∀ j,Set.range (β j) ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).source) ∧
        (∀ j,β j 0 = (a 1).val) ∧
        (∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (β j t) -
          (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val) ∧
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
          {z | (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).symm
            (z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val) ∈
              interior F \ K ∧
            z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).target},
          R.vector 2 = -R.vector 1 := by
    obtain ⟨γ,K₀,hK₀,hpK₀,hcover,hγ,hγstart,hγinside,hγA,hγC,hγmeet⟩ :=
      hActualTerminalConnectorStarFullTrace F c a ha hc hcircle hinside
    obtain ⟨β,d,hd,hd1,hclock,hβ,hβstart,hβsub,hβinside,hβmeet⟩ :=
      hActualFiniteStarInOneChartClocked F γ (a 1).val hγ hγstart hγinside hγmeet
    let l : Interval := ⟨(d:ℝ)/2,by constructor <;> nlinarith [d.property.1,d.property.2]⟩
    have hl : 0 < l := by change (0:ℝ) < (d:ℝ)/2; exact half_pos hd
    let T : Set S := ⋃ j,γ j '' Set.Icc l 1
    have hT : IsCompact T := isCompact_iUnion (fun j =>
      isCompact_Icc.image (γ j).continuous)
    have hpT : (a 1).val ∉ T := by
      intro hp
      obtain ⟨j,t,ht,he⟩ := Set.mem_iUnion.mp hp
      have ht0 : t = 0 := (hγ j).injective (he.trans (hγstart j).symm)
      have hh := ht.1
      rw [ht0] at hh
      exact (not_le_of_gt hl) hh
    let K := K₀ ∪ T
    have hK : IsCompact K := hK₀.union hT
    have hpK : (a 1).val ∉ K := fun h => h.elim hpK₀ hpT
    have hdR : (0:ℝ) < (d:ℝ) := hd
    have hfull : (Set.range (fun t => (a t).val) ∪ c.val.image) ⊆
        K ∪ (⋃ j,Set.range (β j)) := by
      intro y hy
      rcases hcover hy with hk | hg
      · exact Or.inl (Or.inl hk)
      · obtain ⟨j,t,ht⟩ := Set.mem_iUnion.mp hg
        by_cases hlt : l ≤ t
        · left
          right
          exact Set.mem_iUnion.mpr ⟨j,t,⟨hlt,t.property.2⟩,ht⟩
        · right
          apply Set.mem_iUnion.mpr
          refine ⟨j,?_⟩
          have htlt : (t:ℝ) < (d:ℝ)/2 := by
            change ¬ (d:ℝ)/2 ≤ (t:ℝ) at hlt
            exact lt_of_not_ge hlt
          let s : Interval := ⟨(t:ℝ)/(d:ℝ),⟨div_nonneg t.property.1 hd.le,
            (div_le_one hd).mpr (by linarith [hdR])⟩⟩
          refine ⟨s,?_⟩
          rw [hclock]
          refine (congrArg (γ j) (Subtype.ext ?_)).trans ht
          change (d:ℝ)*((t:ℝ)/(d:ℝ))=(t:ℝ)
          field_simp [ne_of_gt hdR]
    obtain ⟨G,hG,R,hR⟩ := hActualTerminalStarRadializationClearance F β (a 1).val
      hβ hβstart hβinside hβmeet K hK hpK
    have hβgraph (j : Fin 3) : Set.range (β j) ⊆
        Set.range (fun t => (a t).val) ∪ c.val.image := by
      intro y hy
      have hh := hβsub j hy
      by_cases hj : j = 0
      · left
        rw [hj] at hh
        exact hγA hh
      · exact Or.inr (hγC j hj hh)
    exact ⟨K,β,G,hK,hpK,hfull,hβ,hβgraph,
      fun j => (hβinside j).trans Set.inter_subset_right,hβstart,hG,R,hR⟩
  have hRadializedWholeGraphCoreExact (γ : Fin 3 → Interval → EuclideanSpace ℝ (Fin 2))
      (V A K : Set (EuclideanSpace ℝ (Fin 2)))
      (R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 V)
      (hcover : A ⊆ K ∪ (⋃ j,Set.range (γ j)))
      (hγA : ∀ j,Set.range (γ j) ⊆ A)
      (hK : Disjoint K (Metric.closedBall 0 R.supportRadius)) :
      (R.H '' A) ∩ Metric.closedBall 0 R.coreRadius =
        (⋃ j,segment ℝ 0 (R.vector j)) ∩ Metric.closedBall 0 R.coreRadius := by
    have hcore : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R.coreRadius ⊆
        Metric.closedBall 0 R.supportRadius := Metric.closedBall_subset_closedBall R.core_lt_support.le
    ext y
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hy⟩
      refine ⟨?_,hy⟩
      rcases hcover hx with hk | hg
      · have hxout : x ∉ Metric.ball 0 R.supportRadius := by
          intro hin
          exact Set.disjoint_left.mp hK hk (Metric.ball_subset_closedBall hin)
        have hfix := R.fixes_exterior x hxout
        have hxcore : x ∈ Metric.closedBall 0 R.coreRadius := hfix ▸ hy
        exact False.elim (Set.disjoint_left.mp hK hk (hcore hxcore))
      · obtain ⟨j,t,ht⟩ := Set.mem_iUnion.mp hg
        have hcut : (t:ℝ) ≤ (R.cut j:ℝ) := by
          by_contra hn
          have htail : R.H x ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
            ⟨x,⟨t,(lt_of_not_ge hn).le,ht⟩,rfl⟩
          exact Set.disjoint_left.mp (R.excludes_tails j) htail hy
        apply Set.mem_iUnion.mpr
        refine ⟨j,?_⟩
        have him : R.H x ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix γ j (R.cut j) := ⟨x,⟨t,hcut,ht⟩,rfl⟩
        rw [R.prefix_image] at him
        simpa only [zero_add] using him
    · rintro ⟨hy,hycore⟩
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
      have hj' : y ∈ segment ℝ 0 (0 + R.vector j) := by simpa only [zero_add] using hj
      rw [← R.prefix_image] at hj'
      obtain ⟨x,⟨t,ht,hxt⟩,hxy⟩ := hj'
      exact ⟨⟨x,hγA j ⟨t,hxt⟩,hxy⟩,hycore⟩
  have hActualChartedWholeGraphCore (F X K : Set S) (p : S)
      (β : Fin 3 → C(Interval,S))
      (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2)))
      (hβchart : ∀ j,Set.range (β j) ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
      (hG : ∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) p) (β j t) -
        (chartAt (EuclideanSpace ℝ (Fin 2)) p) p)
      (hcover : X ⊆ K ∪ (⋃ j,Set.range (β j)))
      (hβX : ∀ j,Set.range (β j) ⊆ X)
      (R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
        {z | (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
          (z+(chartAt (EuclideanSpace ℝ (Fin 2)) p) p) ∈ interior F \ K ∧
          z+(chartAt (EuclideanSpace ℝ (Fin 2)) p) p ∈
            (chartAt (EuclideanSpace ℝ (Fin 2)) p).target}) :
      (R.H '' {z | z+(chartAt (EuclideanSpace ℝ (Fin 2)) p) p ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).target ∧
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
          (z+(chartAt (EuclideanSpace ℝ (Fin 2)) p) p) ∈ X}) ∩
        Metric.closedBall 0 R.coreRadius =
          (⋃ j,segment ℝ 0 (R.vector j)) ∩ Metric.closedBall 0 R.coreRadius := by
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
    let A : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z+e p ∈ e.target ∧ e.symm (z+e p) ∈ X}
    let K' : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z+e p ∈ e.target ∧ e.symm (z+e p) ∈ K}
    have hAc : A ⊆ K' ∪ (⋃ j,Set.range (G j)) := by
      intro z hz
      rcases hcover hz.2 with hk | hb
      · exact Or.inl ⟨hz.1,hk⟩
      · obtain ⟨j,t,ht⟩ := Set.mem_iUnion.mp hb
        right
        apply Set.mem_iUnion.mpr
        refine ⟨j,t,?_⟩
        rw [hG]
        have he : e (β j t) = z+e p := by rw [ht,e.right_inv hz.1]
        change e (β j t)-e p=z
        rw [he]
        abel
    have hGA (j : Fin 3) : Set.range (G j) ⊆ A := by
      rintro z ⟨t,rfl⟩
      have hbt := hβchart j (Set.mem_range_self t)
      have he : G j t+e p=e (β j t) := by rw [hG]; abel
      change G j t+e p ∈ e.target ∧ e.symm (G j t+e p) ∈ X
      rw [he,e.left_inv hbt]
      exact ⟨e.map_source hbt,hβX j (Set.mem_range_self t)⟩
    have hKclear : Disjoint K' (Metric.closedBall 0 R.supportRadius) := by
      apply Set.disjoint_left.mpr
      intro z hz hs
      exact (R.support_subset hs).1.2 hz.2
    exact hRadializedWholeGraphCoreExact (fun j => G j) _ A K' R hAc hGA hKclear
  have hActualTerminalFullTraceCore (F : Set S)
      (c : EssentialCurve S) (a : C(Interval,↥F))
      (ha : Topology.IsEmbedding a) (hc : c.val.image ⊆ interior F)
      (hcircle : ∀ t, (a t).val ∈ c.val.image ↔ t = 1)
      (hinside : ∀ t : Interval, 0 < t → (a t).val ∈ interior F) :
      ∃ (K : Set S) (β : Fin 3 → C(Interval,S))
        (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2))),
        IsCompact K ∧ (a 1).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ c.val.image) ⊆ K ∪ (⋃ j,Set.range (β j)) ∧
        (∀ j,Topology.IsEmbedding (β j)) ∧
        (∀ j,Set.range (β j) ⊆ Set.range (fun t => (a t).val) ∪ c.val.image) ∧
        (∀ j,Set.range (β j) ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).source) ∧
        (∀ j,β j 0 = (a 1).val) ∧
        (∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (β j t) -
          (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val) ∧
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
          {z | (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).symm
            (z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val) ∈
              interior F \ K ∧
            z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).target},
          R.vector 2 = -R.vector 1 ∧
          (R.H '' {z | z+(chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val ∈
            (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).target ∧
            (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).symm
              (z+(chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val) ∈
                Set.range (fun t => (a t).val) ∪ c.val.image}) ∩
            Metric.closedBall 0 R.coreRadius =
              (⋃ j,segment ℝ 0 (R.vector j)) ∩ Metric.closedBall 0 R.coreRadius := by
    obtain ⟨K,β,G,hK,hpK,hfull,hβ,hβgraph,hβchart,hβstart,hG,R,hR⟩ :=
      hActualTerminalFullTraceRadialization F c a ha hc hcircle hinside
    refine ⟨K,β,G,hK,hpK,hfull,hβ,hβgraph,hβchart,hβstart,hG,R,hR,?_⟩
    exact hActualChartedWholeGraphCore F (Set.range (fun t => (a t).val) ∪ c.val.image)
      K (a 1).val β G hβchart hG hfull hβgraph R
  have hActualGenericFullTraceConnectorPortPackage (j : J) :
      ∃ (b : EssentialCurve S) (a : C(Interval,↥F))
        (N : Interval × Set.Icc (-1 : ℝ) 1 → S) (K : Set S)
        (β : Fin 3 → C(Interval,S))
        (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2))),
        Topology.IsEmbedding a ∧ Topology.IsEmbedding N ∧
        b.val.image ⊆ interior F ∧
        Quotient.mk (essentialCurveSetoid S) b = Quotient.mk (essentialCurveSetoid S) (c j) ∧
        (a 0).val ∈ boundaryCircle ∧
        (∀ t,(a t).val ∈ b.val.image ↔ t = 1) ∧
        (∀ t,(a t).val ∈ frontier F ↔ t = 0) ∧
        Set.range N ⊆ interior F \ b.val.image ∧
        (∀ z,N z ∈ Set.range (fun t => (a t).val) ↔ (z.2:ℝ) = 0) ∧
        IsCompact K ∧ (a 1).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ b.val.image) ⊆ K ∪ (⋃ j,Set.range (β j)) ∧
        (∀ j,Topology.IsEmbedding (β j)) ∧
        (∀ j,β j 0 = (a 1).val) ∧
        (∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (β j t) -
          (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val) ∧
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
          {z | (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).symm
            (z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val) ∈
              interior F \ K ∧
            z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).target},
          R.vector 2 = -R.vector 1 := by
    obtain ⟨b,a,ha,hc,hclass,hbase,hcircle,hfrontier,hnepts,hinside⟩ :=
      hActualGenericEssentialCircleEmbeddedCleanAccess j
    let l : Interval := ⟨1/4,by constructor <;> norm_num⟩
    let r : Interval := ⟨3/4,by constructor <;> norm_num⟩
    obtain ⟨N,hN,hNcenter,hNU,hNzero⟩ := hActualEmbeddedConnectorMiddleStrip F b a
      ha hcircle hinside l r (by change (0:ℝ) < 1/4; norm_num)
      (by change (1/4:ℝ) < 3/4; norm_num) (by change (3/4:ℝ) < 1; norm_num)
    obtain ⟨K,β,G,hK,hpK,hfull,hβ,hβgraph,hβchart,hβstart,hG,R,hR⟩ :=
      hActualTerminalFullTraceRadialization F b a ha hc hcircle hinside
    exact ⟨b,a,N,K,β,G,ha,hN,hc,hclass,hbase,hcircle,hfrontier,hNU,hNzero,
      hK,hpK,hfull,hβ,hβstart,hG,R,hR⟩
  have hActualBoundaryConnectorStarFullTrace (F : Set S)
      (c : Curve S) (a : C(Interval,↥(F)))
      (ha : Topology.IsEmbedding a) (hc : c.image ⊆ F)
      (hcircle : ∀ t, (a t).val ∈ c.image ↔ t = 0) :
      ∃ (γ : Fin 3 → C(Interval,S)) (K : Set S),
        IsCompact K ∧ (a 0).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ c.image) ⊆ K ∪ (⋃ j, Set.range (γ j)) ∧
        (∀ j, Topology.IsEmbedding (γ j)) ∧
        (∀ j, γ j 0 = (a 0).val) ∧
        (∀ j, Set.range (γ j) ⊆ F) ∧
        Set.range (γ 0) ⊆ Set.range (fun t => (a t).val) ∧
        (∀ j, j ≠ 0 → Set.range (γ j) ⊆ c.image) ∧
        ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {(a 0).val} := by
    obtain ⟨u,hu⟩ := (hcircle 0).mpr rfl
    let v : Circle := -u
    have hvu : v ≠ u := Circle.neg_ne_self u
    have hxy : (a 0).val ≠ c.map v := by
      intro he
      have huv : u = v := c.embedded.injective (hu.trans he)
      exact hvu huv.symm
    obtain ⟨p,q,hp,hq,hp0,hq0,hp1,hq1,hcover,hmeet⟩ :=
      CurveComplex.source_curve_complementary_arcs c (a 0).val (c.map v)
        ((hcircle 0).mpr rfl) (Set.mem_range_self v) hxy
    let half : C(Interval,Interval) := {
      toFun := fun t => ⟨(t:ℝ)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
    have hhalf : Topology.IsEmbedding half := by
      apply (half.continuous.isClosedEmbedding ?_).isEmbedding
      intro t s he
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      change (t:ℝ)/2=(s:ℝ)/2 at hv
      linarith
    have hh0 : half 0 = 0 := Subtype.ext (by change (0:ℝ)/2=0; ring)
    let back : C(Interval,Interval) := {
      toFun := fun t => ⟨(t:ℝ)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
    have hback : Topology.IsEmbedding back := by
      apply (back.continuous.isClosedEmbedding ?_).isEmbedding
      intro t s he
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      change (t:ℝ)/2=(s:ℝ)/2 at hv
      linarith
    have hb0 : back 0 = 0 := Subtype.ext (by change (0:ℝ)/2=0; ring)
    let f : C(Interval,S) := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
    let A := f.comp back
    let P := p.comp half
    let Q := q.comp half
    have hA : Topology.IsEmbedding A := (Topology.IsEmbedding.subtypeVal.comp ha).comp hback
    have hP : Topology.IsEmbedding P := hp.comp hhalf
    have hQ : Topology.IsEmbedding Q := hq.comp hhalf
    have hA0 : A 0 = (a 0).val := by change f (back 0) = (a 0).val; rw [hb0]; rfl
    have hP0 : P 0 = (a 0).val := by change p (half 0) = (a 0).val; rw [hh0,hp0]
    have hQ0 : Q 0 = (a 0).val := by change q (half 0) = (a 0).val; rw [hh0,hq0]
    have hAsub : Set.range A ⊆ Set.range (fun t => (a t).val) := by
      rintro y ⟨t,rfl⟩
      exact ⟨back t,rfl⟩
    have hPsub : Set.range P ⊆ c.image := by
      rintro y ⟨t,rfl⟩
      rw [← hcover]
      exact Or.inl ⟨half t,rfl⟩
    have hQsub : Set.range Q ⊆ c.image := by
      rintro y ⟨t,rfl⟩
      rw [← hcover]
      exact Or.inr ⟨half t,rfl⟩
    have hAPre : Set.range A ∩ c.image = {(a 0).val} := by
      ext y
      constructor
      · rintro ⟨⟨t,rfl⟩,hcA⟩
        have ht := (hcircle (back t)).mp hcA
        have hv := congrArg Subtype.val ht
        change (t:ℝ)/2=0 at hv
        have ht0 : t = 0 := Subtype.ext (by change (t:ℝ)=0; linarith)
        simpa only [ht0,hA0,Set.mem_singleton_iff]
      · rintro rfl
        exact ⟨⟨0,hA0⟩,(hcircle 0).mpr rfl⟩
    have hAP : Set.range A ∩ Set.range P = {(a 0).val} := by
      apply Set.Subset.antisymm
      · exact (Set.inter_subset_inter_right _ hPsub).trans hAPre.subset
      · rintro y rfl
        exact ⟨⟨0,hA0⟩,⟨0,hP0⟩⟩
    have hAQ : Set.range A ∩ Set.range Q = {(a 0).val} := by
      apply Set.Subset.antisymm
      · exact (Set.inter_subset_inter_right _ hQsub).trans hAPre.subset
      · rintro y rfl
        exact ⟨⟨0,hA0⟩,⟨0,hQ0⟩⟩
    have hPQ : Set.range P ∩ Set.range Q = {(a 0).val} := by
      ext y
      constructor
      · rintro ⟨⟨t,ht⟩,⟨s,hs⟩⟩
        have hym : y ∈ ({(a 0).val,c.map v} : Set S) := by
          rw [← hmeet]
          exact ⟨⟨half t,ht⟩,⟨half s,hs⟩⟩
        rcases hym with hx | hy
        · exact hx
        · have hy' : y = c.map v := hy
          have he : p (half t) = p 1 := ht.trans (hy'.trans hp1.symm)
          have hv := congrArg Subtype.val (hp.injective he)
          change (t:ℝ)/2=1 at hv
          exact False.elim (by linarith [t.property.2])
      · rintro rfl
        exact ⟨⟨0,hP0⟩,⟨0,hQ0⟩⟩
    let γ : Fin 3 → C(Interval,S) := ![A,P,Q]
    let l : Interval := ⟨1/4,by constructor <;> norm_num⟩
    let r : Interval := ⟨3/4,by constructor <;> norm_num⟩
    let K : Set S := (f '' Set.Icc l 1) ∪
      ((p '' Set.Icc l 1) ∪ (q '' Set.Icc l 1))
    have hK : IsCompact K :=
      (isCompact_Icc.image f.continuous).union
        ((isCompact_Icc.image p.continuous).union (isCompact_Icc.image q.continuous))
    have hpK : (a 0).val ∉ K := by
      rintro (hf | hpq)
      · obtain ⟨t,ht,he⟩ := hf
        have ht1 : t = 0 := (Topology.IsEmbedding.subtypeVal.comp ha).injective he
        have hh := ht.1
        rw [ht1] at hh
        change (1/4:ℝ) ≤ 0 at hh
        norm_num at hh
      · rcases hpq with hp' | hq'
        · obtain ⟨t,ht,he⟩ := hp'
          have ht0 : t = 0 := hp.injective (he.trans hp0.symm)
          have hh := ht.1
          rw [ht0] at hh
          change (1/4:ℝ) ≤ 0 at hh
          norm_num at hh
        · obtain ⟨t,ht,he⟩ := hq'
          have ht0 : t = 0 := hq.injective (he.trans hq0.symm)
          have hh := ht.1
          rw [ht0] at hh
          change (1/4:ℝ) ≤ 0 at hh
          norm_num at hh
    have hcoverFull : (Set.range (fun t => (a t).val) ∪ c.image) ⊆
        K ∪ (⋃ j, Set.range (γ j)) := by
      intro y hy
      rcases hy with hf | hc'
      · obtain ⟨t,rfl⟩ := hf
        by_cases ht : l ≤ t
        · exact Or.inl (Or.inl ⟨t,⟨ht,t.property.2⟩,rfl⟩)
        · right
          apply Set.mem_iUnion.mpr
          refine ⟨0,?_⟩
          have htl : (t:ℝ) < (1/4:ℝ) := by
            change ¬ (1/4:ℝ) ≤ (t:ℝ) at ht
            exact lt_of_not_ge ht
          let s : Interval := ⟨2*(t:ℝ),by constructor <;>
            nlinarith [t.property.1,t.property.2]⟩
          refine ⟨s,?_⟩
          change f (back s) = f t
          congr 1
          apply Subtype.ext
          change (2*(t:ℝ))/2=(t:ℝ)
          ring
      · rw [← hcover] at hc'
        rcases hc' with hp' | hq'
        · obtain ⟨t,rfl⟩ := hp'
          by_cases ht : l ≤ t
          · exact Or.inl (Or.inr (Or.inl ⟨t,⟨ht,t.property.2⟩,rfl⟩))
          · right
            apply Set.mem_iUnion.mpr
            refine ⟨1,?_⟩
            have htl : (t:ℝ) < (1/4:ℝ) := by
              change ¬ (1/4:ℝ) ≤ (t:ℝ) at ht
              exact lt_of_not_ge ht
            let s : Interval := ⟨2*(t:ℝ),by constructor <;>
              nlinarith [t.property.1,t.property.2]⟩
            refine ⟨s,?_⟩
            change p (half s) = p t
            congr 1
            apply Subtype.ext
            change (2*(t:ℝ))/2=(t:ℝ)
            ring
        · obtain ⟨t,rfl⟩ := hq'
          by_cases ht : l ≤ t
          · exact Or.inl (Or.inr (Or.inr ⟨t,⟨ht,t.property.2⟩,rfl⟩))
          · right
            apply Set.mem_iUnion.mpr
            refine ⟨2,?_⟩
            have htl : (t:ℝ) < (1/4:ℝ) := by
              change ¬ (1/4:ℝ) ≤ (t:ℝ) at ht
              exact lt_of_not_ge ht
            let s : Interval := ⟨2*(t:ℝ),by constructor <;>
              nlinarith [t.property.1,t.property.2]⟩
            refine ⟨s,?_⟩
            change q (half s) = q t
            congr 1
            apply Subtype.ext
            change (2*(t:ℝ))/2=(t:ℝ)
            ring
    refine ⟨γ,K,hK,hpK,hcoverFull,?_,?_,?_,?_,?_,?_⟩
    · intro j
      fin_cases j <;> assumption
    · intro j
      fin_cases j <;> assumption
    · intro j
      fin_cases j
      · rintro y ⟨t,rfl⟩
        exact (a (back t)).property
      · exact hPsub.trans hc
      · exact hQsub.trans hc
    · exact hAsub
    · intro j hj
      fin_cases j
      · exact False.elim (hj rfl)
      · exact hPsub
      · exact hQsub
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact hAP
      · exact hAQ
      · exact (Set.inter_comm (Set.range P) (Set.range A)).trans hAP
      · exact False.elim (hij rfl)
      · exact hPQ
      · exact (Set.inter_comm (Set.range Q) (Set.range A)).trans hAQ
      · exact (Set.inter_comm (Set.range Q) (Set.range P)).trans hPQ
      · exact False.elim (hij rfl)
  have hActualFiniteStarInOneChartClockedRaw (F : Set S)
      (γ : Fin 3 → C(Interval,S)) (p : S)
      (hγ : ∀ j, Topology.IsEmbedding (γ j))
      (hstart : ∀ j, γ j 0 = p)
      (hinside : ∀ j, Set.range (γ j) ⊆ F)
      (hmeet : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {p}) :
      ∃ (β : Fin 3 → C(Interval,S)) (d : Interval),
        0 < d ∧ d < 1 ∧
        (∀ j t, β j t = γ j ⟨(d:ℝ)*(t:ℝ),by constructor <;> nlinarith [d.property.1,d.property.2,t.property.1,t.property.2]⟩) ∧
        (∀ j, Topology.IsEmbedding (β j)) ∧
        (∀ j, β j 0 = p) ∧
        (∀ j, Set.range (β j) ⊆ Set.range (γ j)) ∧
        (∀ j, Set.range (β j) ⊆ F ∩
          (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) ∧
        ∀ i j, i ≠ j → Set.range (β i) ∩ Set.range (β j) = {p} := by
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
    let W : Set Interval := ⋂ j, γ j ⁻¹' e.source
    have hW : IsOpen W := isOpen_iInter_of_finite (fun j => e.open_source.preimage (γ j).continuous)
    have h0 : (0 : Interval) ∈ W := by
      apply Set.mem_iInter.mpr
      intro j
      change γ j 0 ∈ e.source
      rw [hstart]
      exact ChartedSpace.mem_chart_source p
    obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp hW 0 h0
    let δ : ℝ := min η 1 / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδη : δ < η := by dsimp [δ]; have hh := min_le_left η 1; linarith
    have hδ1 : δ < 1 := by dsimp [δ]; have hh := min_le_right η 1; linarith
    let ρ : C(Interval,Interval) := {
      toFun := fun t => ⟨δ*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop }
    have hρ : Topology.IsEmbedding ρ := by
      apply (ρ.continuous.isClosedEmbedding ?_).isEmbedding
      intro t s he
      apply Subtype.ext
      exact mul_left_cancel₀ (ne_of_gt hδ) (congrArg Subtype.val he)
    have hρ0 : ρ 0 = 0 := Subtype.ext (by change δ*0=0; ring)
    have hρW (t : Interval) : ρ t ∈ W := by
      apply hball
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
      change |δ*(t:ℝ)-0| < η
      rw [sub_zero,abs_of_nonneg (mul_nonneg hδ.le t.property.1)]
      nlinarith [t.property.2]
    let β : Fin 3 → C(Interval,S) := fun j => (γ j).comp ρ
    have hβsub (j : Fin 3) : Set.range (β j) ⊆ Set.range (γ j) := by
      rintro y ⟨t,rfl⟩
      exact ⟨ρ t,rfl⟩
    have hβ0 (j : Fin 3) : β j 0 = p := by change γ j (ρ 0) = p; rw [hρ0,hstart]
    refine ⟨β,⟨δ,⟨hδ.le,hδ1.le⟩⟩,hδ,hδ1,fun j t => rfl,fun j => (hγ j).comp hρ,hβ0,hβsub,?_,?_⟩
    · intro j
      rintro y ⟨t,rfl⟩
      exact ⟨hinside j (Set.mem_range_self (ρ t)),Set.mem_iInter.mp (hρW t) j⟩
    · intro i j hij
      apply Set.Subset.antisymm
      · exact (Set.inter_subset_inter (hβsub i) (hβsub j)).trans (hmeet i j hij).subset
      · rintro y rfl
        exact ⟨⟨0,hβ0 i⟩,⟨0,hβ0 j⟩⟩
  have hActualBoundaryFullTraceRadialization (F : Set S)
      (c : Curve S) (a : C(Interval,↥F))
      (ha : Topology.IsEmbedding a) (hc : c.image ⊆ F)
      (hcircle : ∀ t, (a t).val ∈ c.image ↔ t = 0) :
      ∃ (K : Set S) (β : Fin 3 → C(Interval,S))
        (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2))),
        IsCompact K ∧ (a 0).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ c.image) ⊆ K ∪ (⋃ j,Set.range (β j)) ∧
        (∀ j,Topology.IsEmbedding (β j)) ∧
        (∀ j,Set.range (β j) ⊆ Set.range (fun t => (a t).val) ∪ c.image) ∧
        (∀ j,Set.range (β j) ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).source) ∧
        (∀ j,β j 0 = (a 0).val) ∧
        (∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (β j t) -
          (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val) ∧
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
          {z | (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).symm
            (z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val) ∈
              interior (Set.univ : Set S) \ K ∧
            z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).target},
          R.vector 2 = -R.vector 1 := by
    obtain ⟨γ,K₀,hK₀,hpK₀,hcover,hγ,hγstart,hγinside,hγA,hγC,hγmeet⟩ :=
      hActualBoundaryConnectorStarFullTrace F c a ha hc hcircle
    obtain ⟨β,d,hd,hd1,hclock,hβ,hβstart,hβsub,hβinside,hβmeet⟩ :=
      hActualFiniteStarInOneChartClockedRaw F γ (a 0).val hγ hγstart hγinside hγmeet
    let l : Interval := ⟨(d:ℝ)/2,by constructor <;> nlinarith [d.property.1,d.property.2]⟩
    have hl : 0 < l := by change (0:ℝ) < (d:ℝ)/2; exact half_pos hd
    let T : Set S := ⋃ j,γ j '' Set.Icc l 1
    have hT : IsCompact T := isCompact_iUnion (fun j =>
      isCompact_Icc.image (γ j).continuous)
    have hpT : (a 0).val ∉ T := by
      intro hp
      obtain ⟨j,t,ht,he⟩ := Set.mem_iUnion.mp hp
      have ht0 : t = 0 := (hγ j).injective (he.trans (hγstart j).symm)
      have hh := ht.1
      rw [ht0] at hh
      exact (not_le_of_gt hl) hh
    let K := K₀ ∪ T
    have hK : IsCompact K := hK₀.union hT
    have hpK : (a 0).val ∉ K := fun h => h.elim hpK₀ hpT
    have hdR : (0:ℝ) < (d:ℝ) := hd
    have hfull : (Set.range (fun t => (a t).val) ∪ c.image) ⊆
        K ∪ (⋃ j,Set.range (β j)) := by
      intro y hy
      rcases hcover hy with hk | hg
      · exact Or.inl (Or.inl hk)
      · obtain ⟨j,t,ht⟩ := Set.mem_iUnion.mp hg
        by_cases hlt : l ≤ t
        · left
          right
          exact Set.mem_iUnion.mpr ⟨j,t,⟨hlt,t.property.2⟩,ht⟩
        · right
          apply Set.mem_iUnion.mpr
          refine ⟨j,?_⟩
          have htlt : (t:ℝ) < (d:ℝ)/2 := by
            change ¬ (d:ℝ)/2 ≤ (t:ℝ) at hlt
            exact lt_of_not_ge hlt
          let s : Interval := ⟨(t:ℝ)/(d:ℝ),⟨div_nonneg t.property.1 hd.le,
            (div_le_one hd).mpr (by linarith [hdR])⟩⟩
          refine ⟨s,?_⟩
          rw [hclock]
          refine (congrArg (γ j) (Subtype.ext ?_)).trans ht
          change (d:ℝ)*((t:ℝ)/(d:ℝ))=(t:ℝ)
          field_simp [ne_of_gt hdR]
    obtain ⟨G,hG,R,hR⟩ := hActualTerminalStarRadializationClearance Set.univ β (a 0).val
      hβ hβstart (fun j y hy => ⟨by simp,(hβinside j hy).2⟩) hβmeet K hK hpK
    have hβgraph (j : Fin 3) : Set.range (β j) ⊆
        Set.range (fun t => (a t).val) ∪ c.image := by
      intro y hy
      have hh := hβsub j hy
      by_cases hj : j = 0
      · left
        rw [hj] at hh
        exact hγA hh
      · exact Or.inr (hγC j hj hh)
    exact ⟨K,β,G,hK,hpK,hfull,hβ,hβgraph,
      fun j => (hβinside j).trans Set.inter_subset_right,hβstart,hG,R,hR⟩
  have hActualBoundaryFullTraceCore (F : Set S)
      (c : Curve S) (a : C(Interval,↥F))
      (ha : Topology.IsEmbedding a) (hc : c.image ⊆ F)
      (hcircle : ∀ t, (a t).val ∈ c.image ↔ t = 0) :
      ∃ (K : Set S) (β : Fin 3 → C(Interval,S))
        (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2))),
        IsCompact K ∧ (a 0).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ c.image) ⊆ K ∪ (⋃ j,Set.range (β j)) ∧
        (∀ j,Topology.IsEmbedding (β j)) ∧
        (∀ j,Set.range (β j) ⊆ Set.range (fun t => (a t).val) ∪ c.image) ∧
        (∀ j,Set.range (β j) ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).source) ∧
        (∀ j,β j 0 = (a 0).val) ∧
        (∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (β j t) -
          (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val) ∧
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
          {z | (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).symm
            (z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val) ∈
              interior (Set.univ : Set S) \ K ∧
            z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).target},
          R.vector 2 = -R.vector 1 ∧
          (R.H '' {z | z+(chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val ∈
            (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).target ∧
            (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).symm
              (z+(chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val) ∈
                Set.range (fun t => (a t).val) ∪ c.image}) ∩
            Metric.closedBall 0 R.coreRadius =
              (⋃ j,segment ℝ 0 (R.vector j)) ∩ Metric.closedBall 0 R.coreRadius := by
    obtain ⟨K,β,G,hK,hpK,hfull,hβ,hβgraph,hβchart,hβstart,hG,R,hR⟩ :=
      hActualBoundaryFullTraceRadialization F c a ha hc hcircle
    refine ⟨K,β,G,hK,hpK,hfull,hβ,hβgraph,hβchart,hβstart,hG,R,hR,?_⟩
    exact hActualChartedWholeGraphCore Set.univ (Set.range (fun t => (a t).val) ∪ c.image)
      K (a 0).val β G hβchart hG hfull hβgraph R
  have hActualNormalizedChart (S : Type) [TopologicalSpace S]
      (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
      (p : S) (hp : p ∈ e.source)
      (H : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
      (r : ℝ) (hH0 : H 0=0)
      (hfix : ∀ z,z ∉ Metric.ball 0 r → H z=z)
      (hball : ∀ z ∈ Metric.closedBall 0 r,z+e p ∈ e.target) :
      ∃ E : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)),
        E.source=e.source ∧ E p=0 ∧
        (∀ y,E y=H (e y-e p)) ∧
        Metric.closedBall 0 r ⊆ E.target := by
    have hpres (V : Set (EuclideanSpace ℝ (Fin 2)))
        (hV : Metric.closedBall 0 r ⊆ V) : ∀ z,H z∈V ↔ z∈V := by
      intro z
      by_cases hz : z∈Metric.closedBall 0 r
      · have hHz : H z∈Metric.closedBall 0 r := by
          by_contra hn
          have hnot : H z∉Metric.ball 0 r := fun h => hn (Metric.ball_subset_closedBall h)
          have he : H (H z)=H z := hfix _ hnot
          have hzH : H z=z := H.injective he
          exact hn (hzH.symm ▸ hz)
        exact iff_of_true (hV hHz) (hV hz)
      · rw [hfix z (fun h => hz (Metric.ball_subset_closedBall h))]
    let T := Homeomorph.subRight (e p)
    let E₀ := e.trans T.toOpenPartialHomeomorph
    let E := E₀.trans H.toOpenPartialHomeomorph
    have hsrc : E.source=e.source := by simp [E,E₀,OpenPartialHomeomorph.trans_source]
    have heval (y : S) : E y=H (e y-e p) := rfl
    have htarget : E.target={z | H.symm z+e p∈e.target} := by
      ext z
      simp [E,E₀,T,OpenPartialHomeomorph.trans_target]
    refine ⟨E,hsrc,?_,heval,?_⟩
    · rw [heval,sub_self,hH0]
    · intro z hz
      rw [htarget]
      let V : Set (EuclideanSpace ℝ (Fin 2)) := {w | w+e p∈e.target}
      have hV : Metric.closedBall 0 r ⊆ V := hball
      have h := (hpres V hV (H.symm z)).mp
        (by change H (H.symm z)+e p∈e.target; rw [H.apply_symm_apply]; exact hball z hz)
      exact h
  have hActualNormalizedWholeGraphIncidence (S : Type) [TopologicalSpace S]
      (e E : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
      (p : S) (H : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
      (X Fan : Set (EuclideanSpace ℝ (Fin 2))) (A : Set S) (r : ℝ)
      (hX : X={z | z+e p∈e.target ∧ e.symm (z+e p)∈A})
      (hsrc : E.source=e.source) (heval : ∀ y,E y=H (e y-e p))
      (hcore : (H '' X) ∩ Metric.closedBall 0 r=Fan ∩ Metric.closedBall 0 r) :
      ∀ y∈E.source,E y∈Metric.closedBall 0 r → (y∈A ↔ E y∈Fan) := by
    intro y hy hEy
    have hye : y∈e.source := hsrc ▸ hy
    let z := e y-e p
    have hz : z+e p=e y := sub_add_cancel _ _
    have hza : z∈X ↔ y∈A := by
      rw [hX]
      change (z+e p∈e.target ∧ e.symm (z+e p)∈A) ↔ y∈A
      rw [hz,e.left_inv hye]
      exact and_iff_right (e.map_source hye)
    have hHz : H z=E y := (heval y).symm
    have himage : H z∈H '' X ↔ z∈X := by
      constructor
      · rintro ⟨w,hw,he⟩
        exact H.injective he ▸ hw
      · intro hzX
        exact ⟨z,hzX,rfl⟩
    constructor
    · intro hyA
      have hm : E y∈(H '' X) ∩ Metric.closedBall 0 r :=
        ⟨hHz ▸ (himage.mpr (hza.mpr hyA)),hEy⟩
      rw [hcore] at hm
      exact hm.1
    · intro hyF
      have hm : E y∈(H '' X) ∩ Metric.closedBall 0 r := by
        rw [hcore]
        exact ⟨hyF,hEy⟩
      exact hza.mp (himage.mp (hHz.symm ▸ hm.1))
  have hActualSplitWholeGraphCover (S : Type) (A B K : Set S) (β : Fin 3 → Set S) (p : S)
      (hcover : A ∪ B ⊆ K ∪ (⋃ j,β j))
      (hA : β 0 ⊆ A) (hB : ∀ j,j≠0 → β j ⊆ B)
      (hmeet : A ∩ B={p}) (hp0 : p∈β 0) (hp1 : p∈β 1) :
      (A ⊆ K ∪ β 0) ∧ (B ⊆ K ∪ (⋃ j,⋃ (_ : j≠0),β j)) := by
    constructor
    · intro y hy
      rcases hcover (Or.inl hy) with hk | hb
      · exact Or.inl hk
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hb
        by_cases hj0 : j=0
        · exact Or.inr (hj0 ▸ hj)
        · have hp : y=p := by
            have hh : y∈A ∩ B := ⟨hy,hB j hj0 hj⟩
            rw [hmeet] at hh
            exact hh
          exact Or.inr (hp.symm ▸ hp0)
    · intro y hy
      rcases hcover (Or.inr hy) with hk | hb
      · exact Or.inl hk
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hb
        by_cases hj0 : j=0
        · have hp : y=p := by
            have hh : y∈A ∩ B := ⟨hA (hj0 ▸ hj),hy⟩
            rw [hmeet] at hh
            exact hh
          right
          exact Set.mem_iUnion.mpr ⟨1,Set.mem_iUnion.mpr ⟨by decide,hp.symm ▸ hp1⟩⟩
        · exact Or.inr (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj0,hj⟩⟩)
  have hActualBoundaryFullTraceRadializationSplit (F : Set S)
      (c : Curve S) (a : C(Interval,↥F))
      (ha : Topology.IsEmbedding a) (hc : c.image ⊆ F)
      (hcircle : ∀ t, (a t).val ∈ c.image ↔ t = 0) :
      ∃ (K : Set S) (β : Fin 3 → C(Interval,S))
        (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2))),
        IsCompact K ∧ (a 0).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ c.image) ⊆ K ∪ (⋃ j,Set.range (β j)) ∧
        (Set.range (fun t => (a t).val) ⊆ K ∪ Set.range (β 0)) ∧
        (c.image ⊆ K ∪ (⋃ j,⋃ (_ : j≠0),Set.range (β j))) ∧
        (Set.range (β 0) ⊆ Set.range (fun t => (a t).val)) ∧
        (∀ j,j≠0 → Set.range (β j) ⊆ c.image) ∧
        (∀ j,Topology.IsEmbedding (β j)) ∧
        (∀ j,Set.range (β j) ⊆ Set.range (fun t => (a t).val) ∪ c.image) ∧
        (∀ j,Set.range (β j) ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).source) ∧
        (∀ j,β j 0 = (a 0).val) ∧
        (∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (β j t) -
          (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val) ∧
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
          {z | (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).symm
            (z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val) ∈
              interior (Set.univ : Set S) \ K ∧
            z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).target},
          R.vector 2 = -R.vector 1 := by
    obtain ⟨γ,K₀,hK₀,hpK₀,hcover,hγ,hγstart,hγinside,hγA,hγC,hγmeet⟩ :=
      hActualBoundaryConnectorStarFullTrace F c a ha hc hcircle
    obtain ⟨β,d,hd,hd1,hclock,hβ,hβstart,hβsub,hβinside,hβmeet⟩ :=
      hActualFiniteStarInOneChartClockedRaw F γ (a 0).val hγ hγstart hγinside hγmeet
    let l : Interval := ⟨(d:ℝ)/2,by constructor <;> nlinarith [d.property.1,d.property.2]⟩
    have hl : 0 < l := by change (0:ℝ) < (d:ℝ)/2; exact half_pos hd
    let T : Set S := ⋃ j,γ j '' Set.Icc l 1
    have hT : IsCompact T := isCompact_iUnion (fun j =>
      isCompact_Icc.image (γ j).continuous)
    have hpT : (a 0).val ∉ T := by
      intro hp
      obtain ⟨j,t,ht,he⟩ := Set.mem_iUnion.mp hp
      have ht0 : t = 0 := (hγ j).injective (he.trans (hγstart j).symm)
      have hh := ht.1
      rw [ht0] at hh
      exact (not_le_of_gt hl) hh
    let K := K₀ ∪ T
    have hK : IsCompact K := hK₀.union hT
    have hpK : (a 0).val ∉ K := fun h => h.elim hpK₀ hpT
    have hdR : (0:ℝ) < (d:ℝ) := hd
    have hfull : (Set.range (fun t => (a t).val) ∪ c.image) ⊆
        K ∪ (⋃ j,Set.range (β j)) := by
      intro y hy
      rcases hcover hy with hk | hg
      · exact Or.inl (Or.inl hk)
      · obtain ⟨j,t,ht⟩ := Set.mem_iUnion.mp hg
        by_cases hlt : l ≤ t
        · left
          right
          exact Set.mem_iUnion.mpr ⟨j,t,⟨hlt,t.property.2⟩,ht⟩
        · right
          apply Set.mem_iUnion.mpr
          refine ⟨j,?_⟩
          have htlt : (t:ℝ) < (d:ℝ)/2 := by
            change ¬ (d:ℝ)/2 ≤ (t:ℝ) at hlt
            exact lt_of_not_ge hlt
          let s : Interval := ⟨(t:ℝ)/(d:ℝ),⟨div_nonneg t.property.1 hd.le,
            (div_le_one hd).mpr (by linarith [hdR])⟩⟩
          refine ⟨s,?_⟩
          rw [hclock]
          refine (congrArg (γ j) (Subtype.ext ?_)).trans ht
          change (d:ℝ)*((t:ℝ)/(d:ℝ))=(t:ℝ)
          field_simp [ne_of_gt hdR]
    obtain ⟨G,hG,R,hR⟩ := hActualTerminalStarRadializationClearance Set.univ β (a 0).val
      hβ hβstart (fun j y hy => ⟨by simp,(hβinside j hy).2⟩) hβmeet K hK hpK
    have hβgraph (j : Fin 3) : Set.range (β j) ⊆
        Set.range (fun t => (a t).val) ∪ c.image := by
      intro y hy
      have hh := hβsub j hy
      by_cases hj : j = 0
      · left
        rw [hj] at hh
        exact hγA hh
      · exact Or.inr (hγC j hj hh)
    have hβA : Set.range (β 0) ⊆ Set.range (fun t => (a t).val) :=
      (hβsub 0).trans hγA
    have hβC : ∀ j,j≠0 → Set.range (β j) ⊆ c.image :=
      fun j hj => (hβsub j).trans (hγC j hj)
    have hmeet : Set.range (fun t => (a t).val) ∩ c.image={(a 0).val} := by
      ext y
      constructor
      · rintro ⟨⟨t,ht⟩,hyc⟩
        have ht0 : t=0 := (hcircle t).mp (by simpa only [← ht] using hyc)
        exact Set.mem_singleton_iff.mpr (ht.symm.trans (congrArg (fun t => (a t).val) ht0))
      · rintro rfl
        exact ⟨Set.mem_range_self 0,(hcircle 0).mpr rfl⟩
    obtain ⟨hAcover,hCcover⟩ := hActualSplitWholeGraphCover S
      (Set.range (fun t => (a t).val)) c.image K (fun j => Set.range (β j))
      (a 0).val hfull hβA hβC hmeet ⟨0,hβstart 0⟩ ⟨0,hβstart 1⟩
    exact ⟨K,β,G,hK,hpK,hfull,hAcover,hCcover,hβA,hβC,hβ,hβgraph,
      fun j => (hβinside j).trans Set.inter_subset_right,hβstart,hG,R,hR⟩
  have hRadializedSelectedArmsCoreExact (γ : Fin 3 → CurveComplex.Interval → EuclideanSpace ℝ (Fin 2))
      (V A K : Set (EuclideanSpace ℝ (Fin 2))) (J : Set (Fin 3))
      (R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 V)
      (hcover : A ⊆ K ∪ (⋃ j∈J,Set.range (γ j)))
      (hγA : ∀ j∈J,Set.range (γ j) ⊆ A)
      (hK : Disjoint K (Metric.closedBall 0 R.supportRadius)) :
      (R.H '' A) ∩ Metric.closedBall 0 R.coreRadius =
        (⋃ j∈J,segment ℝ 0 (R.vector j)) ∩ Metric.closedBall 0 R.coreRadius := by
    have hcore : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R.coreRadius ⊆
        Metric.closedBall 0 R.supportRadius := Metric.closedBall_subset_closedBall R.core_lt_support.le
    ext y
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hy⟩
      refine ⟨?_,hy⟩
      rcases hcover hx with hk | hg
      · have hxout : x ∉ Metric.ball 0 R.supportRadius := by
          intro hin
          exact Set.disjoint_left.mp hK hk (Metric.ball_subset_closedBall hin)
        have hfix := R.fixes_exterior x hxout
        have hxcore : x ∈ Metric.closedBall 0 R.coreRadius := hfix ▸ hy
        exact False.elim (Set.disjoint_left.mp hK hk (hcore hxcore))
      · simp only [Set.mem_iUnion] at hg
        obtain ⟨j,hj,t,ht⟩ := hg
        have hcut : (t:ℝ) ≤ (R.cut j:ℝ) := by
          by_contra hn
          have htail : R.H x ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
            ⟨x,⟨t,(lt_of_not_ge hn).le,ht⟩,rfl⟩
          exact Set.disjoint_left.mp (R.excludes_tails j) htail hy
        apply Set.mem_iUnion.mpr
        refine ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩
        have him : R.H x ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix γ j (R.cut j) := ⟨x,⟨t,hcut,ht⟩,rfl⟩
        rw [R.prefix_image] at him
        simpa only [zero_add] using him
    · rintro ⟨hy,hycore⟩
      simp only [Set.mem_iUnion] at hy
      obtain ⟨j,hj,hseg⟩ := hy
      have hj' : y ∈ segment ℝ 0 (0 + R.vector j) := by simpa only [zero_add] using hseg
      rw [← R.prefix_image] at hj'
      obtain ⟨x,⟨t,ht,hxt⟩,hxy⟩ := hj'
      exact ⟨⟨x,hγA j hj ⟨t,hxt⟩,hxy⟩,hycore⟩
  have hActualChartedSelectedGraphCore (F X K : Set S) (J : Set (Fin 3)) (p : S)
      (β : Fin 3 → C(Interval,S))
      (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2)))
      (hβchart : ∀ j,Set.range (β j) ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
      (hG : ∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) p) (β j t) -
        (chartAt (EuclideanSpace ℝ (Fin 2)) p) p)
      (hcover : X ⊆ K ∪ (⋃ j∈J,Set.range (β j)))
      (hβX : ∀ j∈J,Set.range (β j) ⊆ X)
      (R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
        {z | (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
          (z+(chartAt (EuclideanSpace ℝ (Fin 2)) p) p) ∈ interior F \ K ∧
          z+(chartAt (EuclideanSpace ℝ (Fin 2)) p) p ∈
            (chartAt (EuclideanSpace ℝ (Fin 2)) p).target}) :
      (R.H '' {z | z+(chartAt (EuclideanSpace ℝ (Fin 2)) p) p ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).target ∧
        (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
          (z+(chartAt (EuclideanSpace ℝ (Fin 2)) p) p) ∈ X}) ∩
        Metric.closedBall 0 R.coreRadius =
          (⋃ j∈J,segment ℝ 0 (R.vector j)) ∩ Metric.closedBall 0 R.coreRadius := by
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
    let A : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z+e p ∈ e.target ∧ e.symm (z+e p) ∈ X}
    let K' : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z+e p ∈ e.target ∧ e.symm (z+e p) ∈ K}
    have hAc : A ⊆ K' ∪ (⋃ j∈J,Set.range (G j)) := by
      intro z hz
      rcases hcover hz.2 with hk | hb
      · exact Or.inl ⟨hz.1,hk⟩
      · simp only [Set.mem_iUnion] at hb
        obtain ⟨j,hj,t,ht⟩ := hb
        right
        apply Set.mem_iUnion.mpr
        refine ⟨j,Set.mem_iUnion.mpr ⟨hj,t,?_⟩⟩
        rw [hG]
        have he : e (β j t) = z+e p := by rw [ht,e.right_inv hz.1]
        change e (β j t)-e p=z
        rw [he]
        abel
    have hGA (j : Fin 3) (hj : j∈J) : Set.range (G j) ⊆ A := by
      rintro z ⟨t,rfl⟩
      have hbt := hβchart j (Set.mem_range_self t)
      have he : G j t+e p=e (β j t) := by rw [hG]; abel
      change G j t+e p ∈ e.target ∧ e.symm (G j t+e p) ∈ X
      rw [he,e.left_inv hbt]
      exact ⟨e.map_source hbt,hβX j hj (Set.mem_range_self t)⟩
    have hKclear : Disjoint K' (Metric.closedBall 0 R.supportRadius) := by
      apply Set.disjoint_left.mpr
      intro z hz hs
      exact (R.support_subset hs).1.2 hz.2
    exact hRadializedSelectedArmsCoreExact (fun j => G j) _ A K' J R hAc hGA hKclear
  have hActualBoundarySelectedArmChart (F : Set S)
      (c : Curve S) (a : C(Interval,↥F))
      (ha : Topology.IsEmbedding a) (hc : c.image ⊆ F)
      (hcircle : ∀ t, (a t).val ∈ c.image ↔ t = 0) :
      ∃ (K : Set S) (β : Fin 3 → C(Interval,S))
        (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2))),
        IsCompact K ∧ (a 0).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ c.image) ⊆ K ∪ (⋃ j,Set.range (β j)) ∧
        (Set.range (fun t => (a t).val) ⊆ K ∪ Set.range (β 0)) ∧
        (c.image ⊆ K ∪ (⋃ j,⋃ (_ : j≠0),Set.range (β j))) ∧
        (Set.range (β 0) ⊆ Set.range (fun t => (a t).val)) ∧
        (∀ j,j≠0 → Set.range (β j) ⊆ c.image) ∧
        (∀ j,Topology.IsEmbedding (β j)) ∧
        (∀ j,Set.range (β j) ⊆ Set.range (fun t => (a t).val) ∪ c.image) ∧
        (∀ j,Set.range (β j) ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).source) ∧
        (∀ j,β j 0 = (a 0).val) ∧
        (∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (β j t) -
          (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val) ∧
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
          {z | (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).symm
            (z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val) ∈
              interior (Set.univ : Set S) \ K ∧
            z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val) (a 0).val ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).target},
          R.vector 2 = -R.vector 1 ∧
          ∃ E : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)),
            E.source=(chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val).source ∧
            E (a 0).val=0 ∧ Metric.closedBall 0 R.supportRadius ⊆ E.target ∧
            ∀ y∈E.source,E y∈Metric.closedBall 0 R.coreRadius →
              (y∈Set.range (fun t => (a t).val) ↔ E y∈segment ℝ 0 (R.vector 0)) ∧
              (y∈c.image ↔ E y∈⋃ j,⋃ (_ : j≠0),segment ℝ 0 (R.vector j)) := by
    obtain ⟨K,β,G,hK,hpK,hfull,hAcover,hCcover,hβA,hβC,hβ,hβgraph,hβchart,hβstart,hG,R,hR⟩ :=
      hActualBoundaryFullTraceRadializationSplit F c a ha hc hcircle
    let e := chartAt (EuclideanSpace ℝ (Fin 2)) (a 0).val
    obtain ⟨E,hEs,hE0,hEval,hEt⟩ := hActualNormalizedChart S e (a 0).val
      (ChartedSpace.mem_chart_source _) R.H R.supportRadius R.fixes_center R.fixes_exterior
      (fun z hz => (R.support_subset hz).2)
    have hAc : Set.range (fun t => (a t).val) ⊆ K ∪ (⋃ j∈({0} : Set (Fin 3)),Set.range (β j)) := by
      simpa using hAcover
    have hAβ : ∀ j∈({0} : Set (Fin 3)),Set.range (β j) ⊆ Set.range (fun t => (a t).val) := by
      intro j hj
      have hj0 : j=0 := hj
      simpa only [hj0] using hβA
    have hcoreA := hActualChartedSelectedGraphCore Set.univ
      (Set.range (fun t => (a t).val)) K {0} (a 0).val β G hβchart hG hAc hAβ R
    have hcoreA' : (R.H '' {z | z+e (a 0).val∈e.target ∧
        e.symm (z+e (a 0).val)∈Set.range (fun t => (a t).val)}) ∩ Metric.closedBall 0 R.coreRadius =
        segment ℝ 0 (R.vector 0) ∩ Metric.closedBall 0 R.coreRadius := by
      simpa using hcoreA
    have hcoreC := hActualChartedSelectedGraphCore Set.univ c.image K
      {j : Fin 3 | j≠0} (a 0).val β G hβchart hG hCcover hβC R
    refine ⟨K,β,G,hK,hpK,hfull,hAcover,hCcover,hβA,hβC,hβ,hβgraph,hβchart,hβstart,hG,R,hR,
      E,hEs,hE0,hEt,?_⟩
    intro y hy hEy
    constructor
    · exact hActualNormalizedWholeGraphIncidence S e E (a 0).val R.H _ _
        (Set.range (fun t => (a t).val)) R.coreRadius rfl hEs hEval hcoreA' y hy hEy
    · exact hActualNormalizedWholeGraphIncidence S e E (a 0).val R.H _ _
        c.image R.coreRadius rfl hEs hEval hcoreC y hy hEy
  have hThreeRayLinearIndependent (v : Fin 3 → EuclideanSpace ℝ (Fin 2))
      (hn : ∀ j,v j≠0) (hopp : v 2 = -v 1)
      (hd : ∀ i j,i≠j → Disjoint (segment ℝ 0 (v i) \ {0}) (segment ℝ 0 (v j) \ {0})) :
      LinearIndependent ℝ ![v 0,v 1] := by
    have hpos (u w : EuclideanSpace ℝ (Fin 2)) (hw : w≠0)
        (hdis : Disjoint (segment ℝ 0 u \ {0}) (segment ℝ 0 w \ {0}))
        (s : ℝ) (hs : 0<s) : s • w≠u := by
      intro he
      let t : ℝ := min s 1/2
      have ht : 0<t := by dsimp [t]; positivity
      have hts : t ≤ s := by dsimp [t]; have := min_le_left s 1; linarith
      have ht1 : t ≤ 1 := by dsimp [t]; have := min_le_right s 1; linarith
      have hmem (z : EuclideanSpace ℝ (Fin 2)) (a : ℝ) (ha : a∈Set.Icc (0:ℝ) 1) :
          a • z∈segment ℝ 0 z := by
        simpa only [AffineMap.lineMap_apply_module,smul_zero,zero_add] using lineMap_mem_segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) z ha
      have hxw : t • w∈segment ℝ 0 w := hmem w t ⟨ht.le,ht1⟩
      have hxu : t • w∈segment ℝ 0 u := by
        have h := hmem u (t/s) ⟨div_nonneg ht.le hs.le,(div_le_one hs).mpr hts⟩
        rw [←he,smul_smul,div_mul_cancel₀ _ hs.ne'] at h
        simpa only [he] using h
      have hne : t • w≠0 := smul_ne_zero ht.ne' hw
      exact Set.disjoint_left.mp hdis ⟨hxu,hne⟩ ⟨hxw,hne⟩
    apply linearIndependent_fin2.mpr
    refine ⟨hn 1,?_⟩
    intro s he
    by_cases hs : 0<s
    · exact hpos (v 0) (v 1) (hn 1) (hd 0 1 (by decide)) s hs he
    · by_cases hz : s=0
      · exact hn 0 (by simpa [hz] using he.symm)
      · have hneg : s<0 := lt_of_le_of_ne (le_of_not_gt hs) hz
        have he' : (-s) • v 2=v 0 := by rw [hopp,smul_neg,neg_smul,neg_neg]; exact he
        exact hpos (v 0) (v 2) (hn 2) (hd 0 2 (by decide)) (-s) (neg_pos.mpr hneg) he'
  have hTwoRayActualFrame (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) (hv : LinearIndependent ℝ v) :
      ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2),
        (∀ j : Fin 2, L (v j) = EuclideanSpace.single j 1) := by
    let B : Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
      basisOfLinearIndependentOfCardEqFinrank hv
        (by simp [finrank_euclideanSpace_fin])
    let L₀ : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
      B.equivFun
    let L := L₀.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
    refine ⟨L,?_⟩
    intro j
    have hvB : v j=B j := by simp [B]
    rw [hvB]
    change (EuclideanSpace.equiv (Fin 2) ℝ).symm (B.equivFun (B j))=_
    ext i
    change B.equivFun (B j) i = (EuclideanSpace.single j 1) i
    simp [EuclideanSpace.single,Pi.single_apply,Module.Basis.equivFun_self,eq_comm]
  have hFirstAxisSegment (x : EuclideanSpace ℝ (Fin 2)) :
      x∈segment ℝ 0 (EuclideanSpace.single (0 : Fin 2) 1) ↔
        0≤x 0 ∧ x 0≤1 ∧ x 1=0 := by
    rw [segment_eq_image_lineMap]
    constructor
    · rintro ⟨t,ht,rfl⟩
      simpa [AffineMap.lineMap_apply_module,EuclideanSpace.single] using
        And.intro ht.1 (And.intro ht.2 (show (0:ℝ)=0 from rfl))
    · rintro ⟨hx0,hx1,hx2⟩
      refine ⟨x 0,⟨hx0,hx1⟩,?_⟩
      ext i
      fin_cases i
      · simp [AffineMap.lineMap_apply_module,EuclideanSpace.single]
      · simp [AffineMap.lineMap_apply_module,EuclideanSpace.single,hx2]
  have hSecondAxisDoubleSegment (x : EuclideanSpace ℝ (Fin 2)) :
      x∈segment ℝ 0 (EuclideanSpace.single (1 : Fin 2) 1) ∪
        segment ℝ 0 (-EuclideanSpace.single (1 : Fin 2) 1) ↔
        x 0=0 ∧ -1≤x 1 ∧ x 1≤1 := by
    constructor
    · rintro (hx | hx)
      · rw [segment_eq_image_lineMap] at hx
        obtain ⟨t,ht,rfl⟩ := hx
        simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add]
        simp only [PiLp.smul_apply,smul_eq_mul,EuclideanSpace.single_apply,
          Fin.reduceFinMk,ite_false,ite_true,mul_zero,mul_one]
        exact ⟨by norm_num,by linarith [ht.1],ht.2⟩
      · rw [segment_eq_image_lineMap] at hx
        obtain ⟨t,ht,rfl⟩ := hx
        simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add]
        simp only [PiLp.smul_apply,PiLp.neg_apply,smul_eq_mul,EuclideanSpace.single_apply,
          Fin.reduceFinMk,ite_false,ite_true,neg_zero,mul_zero,mul_neg,mul_one]
        exact ⟨by norm_num,by linarith [ht.2],by linarith [ht.1]⟩
    · rintro ⟨hx0,hxlo,hxhi⟩
      by_cases hpos : 0≤x 1
      · left
        rw [segment_eq_image_lineMap]
        refine ⟨x 1,⟨hpos,hxhi⟩,?_⟩
        ext i
        fin_cases i <;> simp [AffineMap.lineMap_apply_module,EuclideanSpace.single,hx0]
      · right
        rw [segment_eq_image_lineMap]
        refine ⟨-x 1,⟨by linarith,by linarith⟩,?_⟩
        ext i
        fin_cases i <;> simp [AffineMap.lineMap_apply_module,EuclideanSpace.single,hx0]
  have hActualRayLineChart (E : OpenPartialHomeomorph S Schoenflies.Plane)
      (p : S) (hp : p∈E.source) (hE0 : E p=0)
      (A B : Set S) (v : Fin 3 → Schoenflies.Plane)
      (hn : ∀ j,v j≠0) (hopp : v 2 = -v 1)
      (hd : ∀ i j,i≠j → Disjoint (segment ℝ 0 (v i) \ {0}) (segment ℝ 0 (v j) \ {0}))
      (r : ℝ) (hr : 0<r) (htarget : Metric.closedBall 0 r ⊆ E.target)
      (hA : ∀ y∈E.source,E y∈Metric.closedBall 0 r → (y∈A ↔ E y∈segment ℝ 0 (v 0)))
      (hB : ∀ y∈E.source,E y∈Metric.closedBall 0 r →
        (y∈B ↔ E y∈⋃ j,⋃ (_ : j≠0),segment ℝ 0 (v j))) :
      ∃ (N : OpenPartialHomeomorph S Schoenflies.Plane) (δ : ℝ),
        N.source=E.source ∧ N p=0 ∧ 0<δ ∧ δ<1 ∧
        Schoenflies.Plane.openSquare 0 δ ⊆ N.target ∧
        ∀ y∈N.source,N y∈Schoenflies.Plane.openSquare 0 δ →
          (y∈A ↔ 0≤N y 0 ∧ N y 1=0) ∧ (y∈B ↔ N y 0=0) := by
    obtain ⟨L,hL⟩ := hTwoRayActualFrame ![v 0,v 1] (hThreeRayLinearIndependent v hn hopp hd)
    have hL0 : L (v 0)=EuclideanSpace.single (0 : Fin 2) 1 := hL 0
    have hL1 : L (v 1)=EuclideanSpace.single (1 : Fin 2) 1 := hL 1
    have hL2 : L (v 2)=-EuclideanSpace.single (1 : Fin 2) 1 := by rw [hopp,map_neg,hL1]
    let N := E.trans L.toHomeomorph.toOpenPartialHomeomorph
    have hNs : N.source=E.source := by simp [N,OpenPartialHomeomorph.trans_source]
    have hNe (y : S) : N y=L (E y) := rfl
    have hN0 : N p=0 := by rw [hNe,hE0,map_zero]
    have hpN : p∈N.source := hNs.symm ▸ hp
    let W : Set Schoenflies.Plane := N.target ∩ L.symm ⁻¹' Metric.ball 0 r
    have hW : IsOpen W := N.open_target.inter (Metric.isOpen_ball.preimage L.symm.continuous)
    have h0W : (0 : Schoenflies.Plane)∈W := by
      have hzL : L.symm (0 : Schoenflies.Plane)=0 := L.symm.map_zero
      have hZ : L.symm (0 : Schoenflies.Plane)∈Metric.ball (0 : Schoenflies.Plane) r := by
        rw [hzL]
        exact Metric.mem_ball.mpr (by simpa only [dist_self] using hr)
      exact ⟨hN0 ▸ N.map_source hpN,hZ⟩
    obtain ⟨δ,hδ,hδ1,hδW⟩ := Schoenflies.Plane.exists_openSquare_subset hW h0W (by norm_num : (0:ℝ)<1/2)
    have hδlt1 : δ<1 := hδ1.trans_lt (by norm_num)
    have hseg (u : Schoenflies.Plane) (y : S) :
        E y∈segment ℝ 0 u ↔ N y∈segment ℝ 0 (L u) := by
      have heq := image_segment ℝ L.toLinearMap.toAffineMap 0 u
      have heq' : L '' segment ℝ 0 u=segment ℝ 0 (L u) := by
        change L '' segment ℝ 0 u=segment ℝ (L 0) (L u) at heq
        simpa only [map_zero] using heq
      rw [←heq',hNe]
      exact ⟨fun h => ⟨E y,h,rfl⟩,fun ⟨z,hz,he⟩ => L.injective he ▸ hz⟩
    refine ⟨N,δ,hNs,hN0,hδ,hδlt1,fun z hz => (hδW hz).1,?_⟩
    intro y hy hysq
    have hyE : y∈E.source := hNs ▸ hy
    have hEy : E y∈Metric.closedBall 0 r := by
      have hh : L.symm (N y)∈Metric.ball (0 : Schoenflies.Plane) r := (hδW hysq).2
      rw [hNe,L.symm_apply_apply] at hh
      exact Metric.ball_subset_closedBall hh
    have hbounds : |N y 0|<δ ∧ |N y 1|<δ := by
      simpa only [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,
        Schoenflies.Plane.supNorm,PiLp.sub_apply,PiLp.zero_apply,sub_zero,max_lt_iff,Set.mem_setOf_eq] using hysq
    constructor
    · rw [hA y hyE hEy,hseg,hL0,hFirstAxisSegment]
      constructor
      · exact fun h => ⟨h.1,h.2.2⟩
      · intro h
        exact ⟨h.1,((abs_lt.mp hbounds.1).2.trans hδlt1).le,h.2⟩
    · rw [hB y hyE hEy]
      have hfan : (N y∈⋃ j,⋃ (_ : j≠0),segment ℝ 0 (L (v j))) ↔
          N y∈segment ℝ 0 (L (v 1)) ∪ segment ℝ 0 (L (v 2)) := by
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨j,hj,hyj⟩
          fin_cases j
          · exact False.elim (hj rfl)
          · exact Or.inl hyj
          · exact Or.inr hyj
        · rintro (h1 | h2)
          · exact ⟨1,by decide,h1⟩
          · exact ⟨2,by decide,h2⟩
      have hfanMap : E y∈⋃ j,⋃ (_ : j≠0),segment ℝ 0 (v j) ↔
          N y∈⋃ j,⋃ (_ : j≠0),segment ℝ 0 (L (v j)) := by
        simp only [Set.mem_iUnion]
        exact exists_congr (fun j => exists_congr (fun _ => hseg (v j) y))
      rw [hfanMap,hfan,hL1,hL2,hSecondAxisDoubleSegment]
      exact ⟨fun h => h.1,fun h => ⟨h,
        (by have hh := (abs_lt.mp hbounds.2).1; linarith),
        ((abs_lt.mp hbounds.2).2.trans hδlt1).le⟩⟩
  have hActualGenericSuppliedConnectorBoundaryRayLine
      (b : Curve S) (hb : b.image=boundaryCircle) (hB : b.image ⊆ F)
      (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcontact : ∀ t,(a t).val∈boundaryCircle ↔ t=0) :
      ∃ (N : OpenPartialHomeomorph S Schoenflies.Plane) (δ : ℝ),
        (a 0).val∈N.source ∧ N (a 0).val=0 ∧ 0<δ ∧ δ<1 ∧
        Schoenflies.Plane.openSquare 0 δ ⊆ N.target ∧
        ∀ y∈N.source,N y∈Schoenflies.Plane.openSquare 0 δ →
          (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
          (y∈boundaryCircle ↔ N y 0=0) := by
    have hcircle : ∀ t,(a t).val∈b.image ↔ t=0 := by simpa only [hb] using hcontact
    obtain ⟨K,β,G,hK,hpK,hfull,hAcover,hCcover,hβA,hβC,
      hβ,hβgraph,hβchart,hβstart,hG,R,hR,E,hEs,hE0,hEt,hinc⟩ :=
      hActualBoundarySelectedArmChart F b a ha hB hcircle
    have hpE : (a 0).val∈E.source := by rw [hEs]; exact ChartedSpace.mem_chart_source _
    have hd : ∀ i j,i≠j → Disjoint (segment ℝ 0 (R.vector i) \ {0})
        (segment ℝ 0 (R.vector j) \ {0}) := by
      intro i j hij
      simpa only [zero_add] using R.distinct_rays i j hij
    obtain ⟨N,δ,hNs,hN0,hδ,hδ1,hδt,hNinc⟩ := hActualRayLineChart E (a 0).val
      hpE hE0 (Set.range (fun t => (a t).val)) b.image R.vector R.vector_nonzero hR hd
      R.coreRadius R.core_pos
      ((Metric.closedBall_subset_closedBall R.core_lt_support.le).trans hEt)
      (fun y hy hs => (hinc y hy hs).1) (fun y hy hs => (hinc y hy hs).2)
    refine ⟨N,δ,hNs.symm ▸ hpE,hN0,hδ,hδ1,hδt,?_⟩
    intro y hy hs
    simpa only [hb] using hNinc y hy hs
  have hActualPositiveRegionLocalHalfPlane (S : Type) [TopologicalSpace S]
      (E : OpenPartialHomeomorph S Schoenflies.Plane) (F : Set S)
      (hF : IsClosed F) (p : S) (hp : p∈E.source) (hEp : E p=0)
      (hpfront : p∈frontier F) (r : ℝ) (hr : 0<r)
      (htarget : Schoenflies.Plane.openSquare 0 r ⊆ E.target)
      (hfrontier : ∀ y∈E.symm '' Schoenflies.Plane.openSquare 0 r,y∈frontier F ↔ E y 0=0)
      (hwitness : ∃ v∈Schoenflies.Plane.openSquare 0 r,0<v 0 ∧ E.symm v∈interior F) :
      ∀ y∈E.symm '' Schoenflies.Plane.openSquare 0 r,
        (y∈F ↔ 0≤E y 0) ∧ (y∈interior F ↔ 0<E y 0) := by
    classical
    let P : Set Schoenflies.Plane := Schoenflies.Plane.openSquare 0 r ∩ {z : Schoenflies.Plane | 0<z 0}
    let M : Set Schoenflies.Plane := Schoenflies.Plane.openSquare 0 r ∩ {z : Schoenflies.Plane | z 0<0}
    have hconvP : Convex ℝ P := by
      intro x hx z hz a b ha hb hab
      refine ⟨(Schoenflies.Plane.convex_openSquare 0 r) hx.1 hz.1 ha hb hab,?_⟩
      change 0<(a • x+b • z) 0
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      have hx1 : 0<x 0 := hx.2
      have hz1 : 0<z 0 := hz.2
      by_cases ha0 : a=0
      · have hb1 : b=1 := by linarith
        simpa [ha0,hb1] using hz1
      · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx1)
          (mul_nonneg hb hz1.le)
    have hconvM : Convex ℝ M := by
      intro x hx z hz a b ha hb hab
      refine ⟨(Schoenflies.Plane.convex_openSquare 0 r) hx.1 hz.1 ha hb hab,?_⟩
      change (a • x+b • z) 0<0
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      have hx1 : x 0<0 := hx.2
      have hz1 : z 0<0 := hz.2
      by_cases ha0 : a=0
      · have hb1 : b=1 := by linarith
        simpa [ha0,hb1] using hz1
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (lt_of_le_of_ne ha (Ne.symm ha0)) hx1)
          (mul_nonpos_of_nonneg_of_nonpos hb hz1.le)
    have hPconn : IsPreconnected (E.symm '' P) := hconvP.isPreconnected.image E.symm
      (E.continuousOn_symm.mono (fun z hz => htarget hz.1))
    have hMconn : IsPreconnected (E.symm '' M) := hconvM.isPreconnected.image E.symm
      (E.continuousOn_symm.mono (fun z hz => htarget hz.1))
    have hPavoid : Disjoint (E.symm '' P) (frontier F) := by
      apply Set.disjoint_left.mpr
      rintro w ⟨z,hz,rfl⟩ hw
      have he := (hfrontier _ ⟨z,hz.1,rfl⟩).mp hw
      rw [E.right_inv (htarget hz.1)] at he
      exact (ne_of_gt hz.2) he
    have hMavoid : Disjoint (E.symm '' M) (frontier F) := by
      apply Set.disjoint_left.mpr
      rintro w ⟨z,hz,rfl⟩ hw
      have he := (hfrontier _ ⟨z,hz.1,rfl⟩).mp hw
      rw [E.right_inv (htarget hz.1)] at he
      exact (ne_of_lt hz.2) he
    let C := E.symm '' Schoenflies.Plane.openSquare 0 r
    have hC : IsOpen C := E.symm.isOpen_image_of_subset_source
      (Schoenflies.Plane.isOpen_openSquare 0 r) htarget
    have hpC : p∈C := by
      refine ⟨0,?_,?_⟩
      · simp [Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,hr]
      · rw [←hEp,E.left_inv hp]
    have hzero (z : Schoenflies.Plane) (hz : z∈Schoenflies.Plane.openSquare 0 r)
        (hz0 : z 0=0) : E.symm z∈frontier F :=
      (hfrontier _ ⟨z,hz,rfl⟩).mpr (by rw [E.right_inv (htarget hz)]; exact hz0)
    have hPin : E.symm '' P ⊆ interior F := by
      rcases connected_cap_side F (E.symm '' P) hPconn hPavoid with hin | hout
      · exact hin
      · obtain ⟨v,hv,hv0,hvI⟩ := hwitness
        exact False.elim ((interior_subset (hout ⟨v,⟨hv,hv0⟩,rfl⟩)) (interior_subset hvI))
    have hMout : E.symm '' M ⊆ interior Fᶜ := by
      rcases connected_cap_side F (E.symm '' M) hMconn hMavoid with hin | hout
      · have hCF : C ⊆ F := by
          rintro y ⟨z,hz,rfl⟩
          rcases lt_trichotomy (z 0) 0 with hn | he | hp'
          · exact interior_subset (hin ⟨z,⟨hz,hn⟩,rfl⟩)
          · exact hF.frontier_subset (hzero z hz he)
          · exact interior_subset (hPin ⟨z,⟨hz,hp'⟩,rfl⟩)
        exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier
          (interior_maximal hCF hC hpC) hpfront)
      · exact hout
    rintro y ⟨z,hz,rfl⟩
    rw [E.right_inv (htarget hz)]
    rcases lt_trichotomy (z 0) 0 with hn | he | hp'
    · have hyout := hMout ⟨z,⟨hz,hn⟩,rfl⟩
      have hyF : E.symm z∉F := interior_subset hyout
      have hyI : E.symm z∉interior F := fun hi => hyF (interior_subset hi)
      exact ⟨iff_of_false hyF (not_le_of_gt hn),iff_of_false hyI (not_lt_of_ge hn.le)⟩
    · have hyfront := hzero z hz he
      have hyF := hF.frontier_subset hyfront
      have hyI : E.symm z∉interior F := fun hi =>
        Set.disjoint_left.mp disjoint_interior_frontier hi hyfront
      exact ⟨iff_of_true hyF (he.symm ▸ le_rfl),iff_of_false hyI (he.symm ▸ lt_irrefl 0)⟩
    · have hyI := hPin ⟨z,⟨hz,hp'⟩,rfl⟩
      exact ⟨iff_of_true (interior_subset hyI) hp'.le,iff_of_true hyI hp'⟩
  have hActualGenericSuppliedConnectorHalfPlane
      (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcontact : ∀ t,(a t).val∈boundaryCircle ↔ t=0)
      (hinside : ∀ t : Interval,0<t → (a t).val∈interior F) :
      ∃ (N : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ),
        (a 0).val∈N.source ∧ N (a 0).val=0 ∧ 0<η ∧ η<1 ∧
        Schoenflies.Plane.openSquare 0 η ⊆ N.target ∧
        ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
          (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
          (y∈boundaryCircle ↔ N y 0=0) ∧
          (y∈F ↔ 0≤N y 0) ∧ (y∈interior F ↔ 0<N y 0) := by
    obtain ⟨b,hb⟩ := hActualChartBoundaryCurve x R hR htarget
    have hb' : b.image=boundaryCircle := hb
    have hB : b.image ⊆ F := hb'.symm ▸ hbase
    obtain ⟨N,δ,hpN,hN0,hδ,hδ1,hδtarget,hinc⟩ :=
      hActualGenericSuppliedConnectorBoundaryRayLine b hb' hB a ha hcontact
    let K : Set S := ⋃ j,(c j).val.image
    have hK : IsCompact K := isCompact_iUnion (fun j => isCompact_range (c j).val.embedded.continuous)
    have hpK : (a 0).val∉K := by
      intro hk
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hk
      exact Set.disjoint_left.mp (hbaseDisjoint j) hj ((hcontact 0).mpr rfl)
    let W : Set Schoenflies.Plane := N.target ∩ N.symm ⁻¹' Kᶜ
    have hW : IsOpen W := N.isOpen_inter_preimage_symm hK.isClosed.isOpen_compl
    have h0W : (0 : Schoenflies.Plane)∈W := by
      have ht0 : (0 : Schoenflies.Plane)∈N.target := hN0 ▸ N.map_source hpN
      have hn : N.symm (0 : Schoenflies.Plane)=(a 0).val := by rw [←hN0,N.left_inv hpN]
      exact ⟨ht0,by change N.symm 0∉K;rw [hn];exact hpK⟩
    obtain ⟨η,hη,hηδ,hηW⟩ := Schoenflies.Plane.exists_openSquare_subset hW h0W (half_pos hδ)
    have hηδ' : η≤δ := hηδ.trans (by linarith)
    have hη1 : η<1 := hηδ'.trans_lt hδ1
    have hsmall : Schoenflies.Plane.openSquare 0 η ⊆ Schoenflies.Plane.openSquare 0 δ :=
      fun z hz => lt_of_lt_of_le hz hηδ'
    have hlocal : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
        (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
        (y∈boundaryCircle ↔ N y 0=0) := by
      rintro y ⟨z,hz,hzy⟩
      have ht := (hηW hz).1
      have hyNs : y∈N.source := hzy ▸ N.map_target ht
      have hNy : N y=z := by rw [←hzy,N.right_inv ht]
      exact hinc y hyNs (hNy.symm ▸ hsmall hz)
    have hfrontN : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
        y∈frontier F ↔ N y 0=0 := by
      intro y hy
      have hyK : y∉K := by obtain ⟨z,hz,hzy⟩ := hy;exact hzy ▸ (hηW hz).2
      rw [hfrontier]
      exact ⟨fun h => (hlocal y hy).2.mp (h.resolve_right hyK),
        fun h => Or.inl ((hlocal y hy).2.mpr h)⟩
    have hwitness : ∃ v∈Schoenflies.Plane.openSquare 0 η,0<v 0 ∧ N.symm v∈interior F := by
      let v := Schoenflies.Plane.mk (η/2) 0
      have hv : v∈Schoenflies.Plane.openSquare 0 η := by
        simp [v,Schoenflies.Plane.openSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,
          Schoenflies.Plane.mk,abs_of_pos (half_pos hη),hη.le]
        linarith
      have hv0 : 0<v 0 := by change 0<η/2;exact half_pos hη
      have hy : N.symm v∈N.symm '' Schoenflies.Plane.openSquare 0 η := ⟨v,hv,rfl⟩
      have hNy : N (N.symm v)=v := N.right_inv (hηW hv).1
      have haR : N.symm v∈Set.range (fun t => (a t).val) := (hlocal _ hy).1.mpr
        (by rw [hNy];exact ⟨hv0.le,by change v 1=0;rfl⟩)
      obtain ⟨t,ht⟩ := haR
      have ht0 : t≠0 := by
        intro he
        have hb0 : N.symm v∈boundaryCircle := by rw [←ht,he];exact (hcontact 0).mpr rfl
        have hz := (hlocal _ hy).2.mp hb0
        rw [hNy] at hz
        exact (ne_of_gt hv0) hz
      exact ⟨v,hv,hv0,ht ▸ hinside t (lt_of_le_of_ne t.property.1 (Ne.symm ht0))⟩
    have hside := hActualPositiveRegionLocalHalfPlane S N F hFclosed (a 0).val hpN hN0
      (hActualBaseInFrontier ((hcontact 0).mpr rfl)) η hη (fun z hz => (hηW hz).1) hfrontN hwitness
    refine ⟨N,η,hpN,hN0,hη,hη1,fun z hz => (hηW hz).1,?_⟩
    intro y hy
    exact ⟨(hlocal y hy).1,(hlocal y hy).2,(hside y hy).1,(hside y hy).2⟩
  have hActualGenericCoherentBothAttachmentPackage (j : J) :
      ∃ (b : EssentialCurve S) (a : C(Interval,↥F))
        (N : Interval × Set.Icc (-1 : ℝ) 1 → S) (K : Set S)
        (β : Fin 3 → C(Interval,S))
        (G : Fin 3 → C(Interval,EuclideanSpace ℝ (Fin 2))),
        Topology.IsEmbedding a ∧ Topology.IsEmbedding N ∧
        b.val.image ⊆ interior F ∧
        Quotient.mk (essentialCurveSetoid S) b = Quotient.mk (essentialCurveSetoid S) (c j) ∧
        (a 0).val ∈ boundaryCircle ∧
        (∀ t,(a t).val ∈ b.val.image ↔ t = 1) ∧
        (∀ t,(a t).val ∈ frontier F ↔ t = 0) ∧
        Set.range N ⊆ interior F \ b.val.image ∧
        (∀ z,N z ∈ Set.range (fun t => (a t).val) ↔ (z.2:ℝ) = 0) ∧
        IsCompact K ∧ (a 1).val ∉ K ∧
        (Set.range (fun t => (a t).val) ∪ b.val.image) ⊆ K ∪ (⋃ j,Set.range (β j)) ∧
        (∀ j,Topology.IsEmbedding (β j)) ∧
        (∀ j,β j 0 = (a 1).val) ∧
        (∀ j t,G j t = (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (β j t) -
          (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val) ∧
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar (fun j => G j) 0
          {z | (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).symm
            (z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val) ∈
              interior F \ K ∧
            z + (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val) (a 1).val ∈
              (chartAt (EuclideanSpace ℝ (Fin 2)) (a 1).val).target},
          R.vector 2 = -R.vector 1 ∧
          ∃ (E : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ),
            (a 0).val∈E.source ∧ E (a 0).val=0 ∧ 0<η ∧ η<1 ∧
            Schoenflies.Plane.openSquare 0 η ⊆ E.target ∧
            ∀ y∈E.symm '' Schoenflies.Plane.openSquare 0 η,
              (y∈Set.range (fun t => (a t).val) ↔ 0≤E y 0 ∧ E y 1=0) ∧
              (y∈boundaryCircle ↔ E y 0=0) ∧
              (y∈F ↔ 0≤E y 0) ∧ (y∈interior F ↔ 0<E y 0) := by
    obtain ⟨b,a,ha,hc,hclass,hbase,hcircle,hfrontier,hnepts,hinside⟩ :=
      hActualGenericEssentialCircleEmbeddedCleanAccess j
    let l : Interval := ⟨1/4,by constructor <;> norm_num⟩
    let r : Interval := ⟨3/4,by constructor <;> norm_num⟩
    obtain ⟨N,hN,hNcenter,hNU,hNzero⟩ := hActualEmbeddedConnectorMiddleStrip F b a
      ha hcircle hinside l r (by change (0:ℝ) < 1/4; norm_num)
      (by change (1/4:ℝ) < 3/4; norm_num) (by change (3/4:ℝ) < 1; norm_num)
    obtain ⟨K,β,G,hK,hpK,hfull,hβ,hβgraph,hβchart,hβstart,hG,R,hR⟩ :=
      hActualTerminalFullTraceRadialization F b a ha hc hcircle hinside
    have hcontact : ∀ t,(a t).val∈boundaryCircle ↔ t=0 := by
      intro t
      exact ⟨fun ht => (hfrontier t).mp (hActualBaseInFrontier ht),fun ht => ht.symm ▸ hbase⟩
    obtain ⟨E,η,hpE,hE0,hη,hη1,hηt,hlocal⟩ :=
      hActualGenericSuppliedConnectorHalfPlane a ha hcontact hinside
    exact ⟨b,a,N,K,β,G,ha,hN,hc,hclass,hbase,hcircle,hfrontier,hNU,hNzero,
      hK,hpK,hfull,hβ,hβstart,hG,R,hR,E,η,hpE,hE0,hη,hη1,hηt,hlocal⟩
  have hActualGenericSuppliedConnectorInitialBand
      (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcontact : ∀ t,(a t).val∈boundaryCircle ↔ t=0)
      (hinside : ∀ t : Interval,0<t → (a t).val∈interior F) :
      ∃ b : ℝ,∃ hb : 0<b ∧ b<1,
      ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F),
        Topology.IsEmbedding E ∧
        (∀ t,E (t,⟨0,by norm_num⟩)=
          a ⟨b*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
        (∀ w,(E (0,w)).val∈boundaryCircle) ∧
        (∀ t : Interval,0<(t:ℝ) → ∀ w,
          (E (t,w)).val∈interior F ∧ (E (t,w)).val∉boundaryCircle) ∧
        ∀ z,E z∈Set.range a ↔ (z.2:ℝ)=0 := by
    obtain ⟨N,η,hpN,hN0,hη,hη1,hηtarget,hlocal⟩ :=
      hActualGenericSuppliedConnectorHalfPlane a ha hcontact hinside
    obtain ⟨b,hb,E,hE,hcenter,hbase,hinside,htrace,hchart⟩ :=
      actual_one_endpoint_regional_full_width_band F boundaryCircle a ha
        hcontact N η hpN hN0 hη hηtarget hlocal
    exact ⟨b,hb,E,hE,hcenter,hbase,hinside,htrace⟩
  have hActualSuppliedCurveConnectorRayLine (F B : Set S)
      (b : Curve S) (hb : b.image=B) (hB : b.image ⊆ F)
      (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcontact : ∀ t,(a t).val∈B ↔ t=0) :
      ∃ (N : OpenPartialHomeomorph S Schoenflies.Plane) (δ : ℝ),
        (a 0).val∈N.source ∧ N (a 0).val=0 ∧ 0<δ ∧ δ<1 ∧
        Schoenflies.Plane.openSquare 0 δ ⊆ N.target ∧
        ∀ y∈N.source,N y∈Schoenflies.Plane.openSquare 0 δ →
          (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
          (y∈B ↔ N y 0=0) := by
    have hcircle : ∀ t,(a t).val∈b.image ↔ t=0 := by simpa only [hb] using hcontact
    obtain ⟨K,β,G,hK,hpK,hfull,hAcover,hCcover,hβA,hβC,
      hβ,hβgraph,hβchart,hβstart,hG,R,hR,E,hEs,hE0,hEt,hinc⟩ :=
      hActualBoundarySelectedArmChart F b a ha hB hcircle
    have hpE : (a 0).val∈E.source := by rw [hEs]; exact ChartedSpace.mem_chart_source _
    have hd : ∀ i j,i≠j → Disjoint (segment ℝ 0 (R.vector i) \ {0})
        (segment ℝ 0 (R.vector j) \ {0}) := by
      intro i j hij
      simpa only [zero_add] using R.distinct_rays i j hij
    obtain ⟨N,δ,hNs,hN0,hδ,hδ1,hδt,hNinc⟩ := hActualRayLineChart E (a 0).val
      hpE hE0 (Set.range (fun t => (a t).val)) b.image R.vector R.vector_nonzero hR hd
      R.coreRadius R.core_pos
      ((Metric.closedBall_subset_closedBall R.core_lt_support.le).trans hEt)
      (fun y hy hs => (hinc y hy hs).1) (fun y hy hs => (hinc y hy hs).2)
    refine ⟨N,δ,hNs.symm ▸ hpE,hN0,hδ,hδ1,hδt,?_⟩
    intro y hy hs
    simpa only [hb] using hNinc y hy hs
  have hActualSuppliedConnectorTerminalRayLine (F : Set S)
      (c : Curve S) (hc : c.image ⊆ interior F)
      (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcircle : ∀ t,(a t).val∈c.image ↔ t=1) :
      ∃ (N : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ),
        (a 1).val∈N.source ∧ N (a 1).val=0 ∧ 0<η ∧ η<1 ∧
        Schoenflies.Plane.openSquare 0 η ⊆ N.target ∧
        ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
          y∈interior F ∧
          (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
          (y∈c.image ↔ N y 0=0) := by
    let ρ : C(Interval,Interval) := ⟨unitInterval.symm,unitInterval.continuous_symm⟩
    have hρ : Topology.IsEmbedding ρ :=
      (ρ.continuous.isClosedEmbedding unitInterval.symm_involutive.injective).isEmbedding
    let rev : C(Interval,↥F) := a.comp ρ
    have hrev : Topology.IsEmbedding rev := ha.comp hρ
    have hrev0 : (rev 0).val=(a 1).val := by simp [rev,ρ]
    have hcontact : ∀ t,(rev t).val∈c.image ↔ t=0 := by
      intro t
      change (a (unitInterval.symm t)).val∈c.image ↔ t=0
      rw [hcircle]
      constructor
      · intro he
        apply Subtype.ext
        have hv := congrArg Subtype.val he
        change 1-(t:ℝ)=1 at hv
        change (t:ℝ)=0
        linarith
      · rintro rfl
        simp
    have htrace : Set.range (fun t => (rev t).val)=Set.range (fun t => (a t).val) := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨unitInterval.symm t,?_⟩
        change (a (unitInterval.symm (unitInterval.symm t))).val=(a t).val
        rw [unitInterval.symm_involutive t]
    obtain ⟨N,δ,hpN,hN0,hδ,hδ1,hδtarget,hinc⟩ :=
      hActualSuppliedCurveConnectorRayLine F c.image c rfl (hc.trans interior_subset) rev hrev hcontact
    have hpI : (rev 0).val∈interior F := by rw [hrev0];exact hc ((hcircle 1).mpr rfl)
    let W : Set Schoenflies.Plane := N.target ∩ N.symm ⁻¹' interior F
    have hW : IsOpen W := N.isOpen_inter_preimage_symm isOpen_interior
    have h0W : (0 : Schoenflies.Plane)∈W := by
      have ht0 : (0 : Schoenflies.Plane)∈N.target := hN0 ▸ N.map_source hpN
      have hn : N.symm (0 : Schoenflies.Plane)=(rev 0).val := by rw [←hN0,N.left_inv hpN]
      exact ⟨ht0,by change N.symm 0∈interior F;rw [hn];exact hpI⟩
    obtain ⟨η,hη,hηδ,hηW⟩ := Schoenflies.Plane.exists_openSquare_subset hW h0W (half_pos hδ)
    have hηδ' : η≤δ := hηδ.trans (by linarith)
    have hη1 : η<1 := hηδ'.trans_lt hδ1
    have hsmall : Schoenflies.Plane.openSquare 0 η ⊆ Schoenflies.Plane.openSquare 0 δ :=
      fun z hz => lt_of_lt_of_le hz hηδ'
    refine ⟨N,η,hrev0 ▸ hpN,hrev0 ▸ hN0,hη,hη1,fun z hz => (hηW hz).1,?_⟩
    rintro y ⟨z,hz,hzy⟩
    have ht := (hηW hz).1
    have hyNs : y∈N.source := hzy ▸ N.map_target ht
    have hNy : N y=z := by rw [←hzy,N.right_inv ht]
    have hyI : y∈interior F := hzy ▸ (hηW hz).2
    refine ⟨hyI,?_⟩
    simpa only [htrace] using hinc y hyNs (hNy.symm ▸ hsmall hz)
  have hActualTerminalTransverseCap (S : Type) [TopologicalSpace S] [T2Space S]
      (F A B : Set S) (N : OpenPartialHomeomorph S Schoenflies.Plane)
      (η : ℝ) (hη : 0<η) (ht : Schoenflies.Plane.openSquare 0 η ⊆ N.target)
      (hl : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
        y∈interior F ∧ (y∈A ↔ 0≤N y 0 ∧ N y 1=0) ∧ (y∈B ↔ N y 0=0))
      (ε w : ℝ) (hε : 0<ε) (hεη : ε<η) (hw : |w|<η) (hw0 : w≠0) :
      ∃ cap : C(Interval,S),Topology.IsEmbedding cap ∧
        (∀ t,cap t∈interior F ∧ cap t∉A ∧ (cap t∈B ↔ t=1)) ∧
        ∀ t,N (cap t)=Schoenflies.Plane.mk (ε*(1-(t:ℝ))) w := by
    let k : C(Interval,Schoenflies.Plane) := ⟨fun t => Schoenflies.Plane.mk (ε*(1-(t:ℝ))) w,by
      dsimp [Schoenflies.Plane.mk];fun_prop⟩
    have hk : ∀ t,k t∈Schoenflies.Plane.openSquare 0 η := by
      intro t
      rw [Schoenflies.Plane.mem_openSquare_iff]
      intro i
      fin_cases i
      · change |ε*(1-(t:ℝ))-0|<η
        rw [sub_zero,abs_of_nonneg (mul_nonneg hε.le (sub_nonneg.mpr t.property.2))]
        exact (mul_le_of_le_one_right hε.le (by linarith [t.property.1])).trans_lt hεη
      · simpa [k,Schoenflies.Plane.mk] using hw
    let cap : C(Interval,S) := ⟨fun t => N.symm (k t),
      N.continuousOn_symm.comp_continuous k.continuous (fun t => ht (hk t))⟩
    have hNc : ∀ t,N (cap t)=k t := fun t => N.right_inv (ht (hk t))
    have hi : Function.Injective cap := by
      intro t s he
      have hv := congrArg (fun y => N y 0) he
      rw [hNc t,hNc s] at hv
      change ε*(1-(t:ℝ))=ε*(1-(s:ℝ)) at hv
      apply Subtype.ext
      have heq := mul_left_cancel₀ hε.ne' hv
      linarith
    refine ⟨cap,(cap.continuous.isClosedEmbedding hi).isEmbedding,?_,hNc⟩
    intro t
    have htlocal := hl (cap t) ⟨k t,hk t,rfl⟩
    refine ⟨htlocal.1,?_,?_⟩
    · intro hA
      have hz := (htlocal.2.1.mp hA).2
      rw [hNc t] at hz
      exact hw0 hz
    · rw [htlocal.2.2,hNc t]
      change ε*(1-(t:ℝ))=0 ↔ t=1
      constructor
      · intro he
        have hh := (mul_eq_zero.mp he).resolve_left hε.ne'
        apply Subtype.ext
        change (t:ℝ)=1
        linarith
      · rintro rfl
        change ε*(1-1)=0
        ring
  have hActualCurveComplementaryArcAvoiding (S : Type) [TopologicalSpace S] [T2Space S]
      (c : Curve S) (x y z : S) (hx : x∈c.image) (hy : y∈c.image)
      (hxy : x≠y) (hzx : z≠x) (hzy : z≠y) :
      ∃ p : C(Interval,S),Topology.IsEmbedding p ∧ p 0=x ∧ p 1=y ∧
        Set.range p ⊆ c.image ∧ z∉Set.range p := by
    obtain ⟨p,q,hp,hq,hp0,hq0,hp1,hq1,hcover,hmeet⟩ :=
      source_curve_complementary_arcs c x y hx hy hxy
    have hpC : Set.range p ⊆ c.image := by rw [←hcover];exact Set.subset_union_left
    have hqC : Set.range q ⊆ c.image := by rw [←hcover];exact Set.subset_union_right
    by_cases hzp : z∈Set.range p
    · refine ⟨q,hq,hq0,hq1,hqC,?_⟩
      intro hzq
      have hz : z∈({x,y} : Set S) := hmeet ▸ ⟨hzp,hzq⟩
      simpa [hzx,hzy] using hz
    · exact ⟨p,hp,hp0,hp1,hpC,hzp⟩
  have hActualTerminalCircleBypass (F : Set S) (c : Curve S) (hc : c.image ⊆ interior F)
      (a : C(Interval,↥F)) (hcircle : ∀ t,(a t).val∈c.image ↔ t=1)
      (N : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ) (hη : 0<η)
      (htarget : Schoenflies.Plane.openSquare 0 η ⊆ N.target)
      (hlocal : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
        y∈interior F ∧
        (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
        (y∈c.image ↔ N y 0=0)) :
      ∃ (ε : ℝ) (r : C(Interval,S)),0<ε ∧ ε<η ∧ Topology.IsEmbedding r ∧
        N (r 0)=Schoenflies.Plane.mk ε ε ∧ N (r 1)=Schoenflies.Plane.mk ε (-ε) ∧
        Set.range r ⊆ interior F ∧
        Disjoint (Set.range r) (Set.range (fun t => (a t).val)) := by
    let ε : ℝ := η/2
    have hε : 0<ε := half_pos hη
    have hεη : ε<η := by dsimp [ε];linarith
    obtain ⟨P,hP,hPl,hPN⟩ := hActualTerminalTransverseCap S F
      (Set.range (fun t => (a t).val)) c.image N η hη htarget hlocal ε ε hε hεη
      (by rwa [abs_of_pos hε]) hε.ne'
    obtain ⟨Q,hQ,hQl,hQN⟩ := hActualTerminalTransverseCap S F
      (Set.range (fun t => (a t).val)) c.image N η hη htarget hlocal ε (-ε) hε hεη
      (by rw [abs_neg,abs_of_pos hε];exact hεη) (neg_ne_zero.mpr hε.ne')
    have hPQ : Disjoint (Set.range P) (Set.range Q) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨s,rfl⟩ ⟨t,he⟩
      have hz := congrArg (fun y => N y 1) he
      rw [hQN t,hPN s] at hz
      change -ε=ε at hz
      linarith
    have hends : P 1≠Q 1 := fun he => Set.disjoint_left.mp hPQ
      (Set.mem_range_self 1) ⟨1,he.symm⟩
    have hjP : (a 1).val≠P 1 := by
      intro he
      exact (hPl 1).2.1 (he ▸ Set.mem_range_self 1)
    have hjQ : (a 1).val≠Q 1 := by
      intro he
      exact (hQl 1).2.1 (he ▸ Set.mem_range_self 1)
    obtain ⟨d,hd,hd0,hd1,hdc,hdj⟩ := hActualCurveComplementaryArcAvoiding S c (P 1) (Q 1)
      (a 1).val ((hPl 1).2.2.mpr rfl) ((hQl 1).2.2.mpr rfl) hends hjP hjQ
    let p : Path (P 0) (P 1) := ⟨P,rfl,rfl⟩
    let q : Path (P 1) (Q 1) := ⟨d,hd0,hd1⟩
    let m : Path (Q 0) (Q 1) := ⟨Q,rfl,rfl⟩
    have hpq : Set.range p ∩ Set.range q={P 1} := by
      ext y
      constructor
      · rintro ⟨⟨t,ht⟩,hyq⟩
        have ht1 : t=1 := (hPl t).2.2.mp (ht.symm ▸ hdc hyq)
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg p ht1).trans p.target))
      · rintro rfl
        exact ⟨⟨1,rfl⟩,⟨0,hd0⟩⟩
    have hqm : Set.range q ∩ Set.range m.symm={Q 1} := by
      rw [Path.symm_range]
      ext y
      constructor
      · rintro ⟨hyq,⟨t,ht⟩⟩
        have ht1 : t=1 := (hQl t).2.2.mp (ht.symm ▸ hdc hyq)
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg m ht1).trans m.target))
      · rintro rfl
        exact ⟨⟨1,hd1⟩,⟨1,rfl⟩⟩
    have hjoin : Set.range (p.trans q) ∩ Set.range m.symm={Q 1} := by
      rw [Path.trans_range,Set.union_inter_distrib_right,hqm,Path.symm_range]
      have he : Set.range p ∩ Set.range m=∅ := Set.disjoint_iff_inter_eq_empty.mp hPQ
      rw [he,Set.empty_union]
    have hpqi := hSimpleConcat p q hP.injective hd.injective hpq
    have hi := hSimpleConcat (p.trans q) m.symm hpqi
      (hQ.injective.comp unitInterval.symm_involutive.injective) hjoin
    let r : C(Interval,S) := ⟨(p.trans q).trans m.symm,((p.trans q).trans m.symm).continuous⟩
    have hrange : Set.range r=(Set.range P ∪ Set.range d) ∪ Set.range Q := by
      change Set.range ((p.trans q).trans m.symm)=_
      rw [Path.trans_range,Path.trans_range,Path.symm_range]
      rfl
    refine ⟨ε,r,hε,hεη,(r.continuous.isClosedEmbedding hi).isEmbedding,?_,?_,?_,?_⟩
    · change N (((p.trans q).trans m.symm) 0)=_
      rw [Path.source]
      simpa using hPN 0
    · change N (((p.trans q).trans m.symm) 1)=_
      rw [Path.target]
      simpa using hQN 0
    · rw [hrange]
      exact Set.union_subset (Set.union_subset (by rintro y ⟨t,rfl⟩;exact (hPl t).1)
        (hdc.trans hc)) (by rintro y ⟨t,rfl⟩;exact (hQl t).1)
    · apply Set.disjoint_left.mpr
      rw [hrange]
      intro y hyr hya
      rcases hyr with (hyP | hyd) | hyQ
      · obtain ⟨t,rfl⟩ := hyP
        exact (hPl t).2.1 hya
      · obtain ⟨t,ht⟩ := hya
        have hty : (a t).val=y := ht
        have htc : (a t).val∈c.image := hty.symm ▸ hdc hyd
        have ht1 : t=1 := (hcircle t).mp htc
        exact hdj ((by rw [←ht,ht1] : y=(a 1).val) ▸ hyd)
      · obtain ⟨t,rfl⟩ := hyQ
        exact (hQl t).2.1 hya
  have hActualChartHalfRegion (S : Type) [TopologicalSpace S]
      (F : Set S) (N : OpenPartialHomeomorph S Schoenflies.Plane)
      (η : ℝ) (hη : 0<η) (ht : Schoenflies.Plane.openSquare 0 η ⊆ N.target)
      (hI : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,y∈interior F) :
      let O := N.symm '' (Schoenflies.Plane.openSquare 0 η ∩ {z : Schoenflies.Plane | z 0<0})
      let R := F \ O
      ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
        (y∈R ↔ 0≤N y 0) ∧ (y∈interior R ↔ 0<N y 0) := by
    dsimp only
    let O := N.symm '' (Schoenflies.Plane.openSquare 0 η ∩ {z : Schoenflies.Plane | z 0<0})
    let R := F \ O
    rintro y hy
    obtain ⟨z,hz,hzy⟩ := hy
    have hyN : y∈N.source := hzy ▸ N.map_target (ht hz)
    have hNy : N y=z := by rw [←hzy,N.right_inv (ht hz)]
    have hySq : N y∈Schoenflies.Plane.openSquare 0 η := hNy.symm ▸ hz
    have hyI : y∈interior F := hI y ⟨z,hz,hzy⟩
    have hyO : y∈O ↔ N y 0<0 := by
      constructor
      · rintro ⟨v,hv,hvy⟩
        have hn : N y=v := by rw [←hvy,N.right_inv (ht hv.1)]
        exact hn.symm ▸ hv.2
      · intro hn
        exact ⟨N y,⟨hySq,hn⟩,N.left_inv hyN⟩
    have hyR : y∈R ↔ 0≤N y 0 := by
      change (y∈F ∧ y∉O) ↔ 0≤N y 0
      rw [hyO]
      exact ⟨fun h => le_of_not_gt h.2,fun h => ⟨interior_subset hyI,not_lt_of_ge h⟩⟩
    refine ⟨hyR,?_⟩
    constructor
    · intro hyIR
      have hnonneg := hyR.mp (interior_subset hyIR)
      apply lt_of_le_of_ne hnonneg
      intro hzero
      have hz0 : N y 0=0 := hzero.symm
      let U : Set S := interior R ∩ N.source
      have hU : IsOpen U := isOpen_interior.inter N.open_source
      have hV : IsOpen (N '' U) := N.isOpen_image_of_subset_source hU Set.inter_subset_right
      have hzV : N y∈N '' U := ⟨y,⟨hyIR,hyN⟩,rfl⟩
      have hW : IsOpen (N '' U ∩ Schoenflies.Plane.openSquare 0 η) :=
        hV.inter (Schoenflies.Plane.isOpen_openSquare 0 η)
      obtain ⟨δ,hδ,hδ1,hδW⟩ := Schoenflies.Plane.exists_openSquare_subset hW ⟨hzV,hySq⟩
        (by norm_num : (0:ℝ)<1)
      let v := Schoenflies.Plane.mk (-δ/2) (N y 1)
      have hv : v∈Schoenflies.Plane.openSquare (N y) δ := by
        change max |-δ/2-N y 0| |N y 1-N y 1|<δ
        rw [hz0,sub_zero,sub_self,abs_zero,neg_div,abs_neg,abs_of_pos (half_pos hδ),max_eq_left (half_pos hδ).le]
        linarith
      obtain ⟨w,hw,hNv⟩ := (hδW hv).1
      have hwO : w∈O := by
        refine ⟨v,⟨(hδW hv).2,?_⟩,?_⟩
        · change -δ/2<0;linarith
        · rw [←hNv,N.left_inv hw.2]
      exact (interior_subset hw.1).2 hwO
    · intro hypos
      let P := Schoenflies.Plane.openSquare 0 η ∩ {v : Schoenflies.Plane | 0<v 0}
      have hP : IsOpen P := (Schoenflies.Plane.isOpen_openSquare 0 η).inter
        (isOpen_lt continuous_const (by fun_prop))
      have hPU : IsOpen (N.symm '' P) := N.symm.isOpen_image_of_subset_source hP
        (fun v hv => ht hv.1)
      have hsub : N.symm '' P ⊆ R := by
        rintro u ⟨v,hv,rfl⟩
        refine ⟨interior_subset (hI _ ⟨v,hv.1,rfl⟩),?_⟩
        rintro ⟨v',hv',he⟩
        have hvv : v'=v := N.symm.injOn (ht hv'.1) (ht hv.1) he
        have hneg : v 0<0 := hvv ▸ hv'.2
        exact (not_lt_of_gt hv.2) hneg
      apply interior_maximal hsub hPU
      exact ⟨N y,⟨hySq,hypos⟩,N.left_inv hyN⟩
  have hActualGenericTwoNegativeAccessContinuations
      (c₀ : Curve S) (hc₀ : c₀.image⊆interior F)
      (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcontact : ∀ t,(a t).val∈boundaryCircle ↔ t=0)
      (hinside : ∀ t : Interval,0<t → (a t).val∈interior F)
      (hcircle : ∀ t,(a t).val∈c₀.image ↔ t=1) :
      ∃ r₀ r₁ : C(Interval,S),
        Topology.IsEmbedding r₀ ∧ Topology.IsEmbedding r₁ ∧
        r₀ 0=(a 0).val ∧ r₁ 0=(a 1).val ∧
        (∀ t : Interval,0<t → r₀ t∉F) ∧
        (∀ t,r₁ t∈interior F) ∧
        (∀ t : Interval,0<t → r₁ t∉c₀.image) ∧
        Set.range r₀ ∩ Set.range (fun t => (a t).val)={(a 0).val} ∧
        Set.range r₁ ∩ Set.range (fun t => (a t).val)={(a 1).val} ∧
        Disjoint (Set.range r₀) (Set.range r₁) := by
    obtain ⟨N₀,η₀,hp₀,hz₀,hη₀,_,ht₀,hl₀⟩ :=
      hActualGenericSuppliedConnectorHalfPlane a ha hcontact hinside
    obtain ⟨r₀,hr₀,hr₀zero,hr₀out,hr₀trace,_⟩ :=
      actual_negative_chart_halfplane_ray_from_positive_square
        F a N₀ η₀ hp₀ hz₀ hη₀ ht₀ (fun y hy => (hl₀ y hy).2.2.1)
    obtain ⟨N₁,η₁,hp₁,hz₁,hη₁,_,ht₁,hl₁⟩ :=
      hActualSuppliedConnectorTerminalRayLine F c₀ hc₀ a ha hcircle
    obtain ⟨r₁,hr₁,hr₁zero,hr₁inside,hr₁off,hr₁trace,_⟩ :=
      actual_negative_terminal_chart_ray_beyond_essential_circle
        F c₀.image a N₁ η₁ hp₁ hz₁ hη₁ ht₁ hl₁
    have hd : Disjoint (Set.range r₀) (Set.range r₁) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨t,ht⟩ ⟨u,hu⟩
      have hyI : r₀ t∈interior F := ht ▸ hu.symm ▸ hr₁inside u
      by_cases ht0 : t=0
      · have ha0I : (a 0).val∈interior F := by simpa only [ht0,hr₀zero] using hyI
        have ha0front : (a 0).val∈frontier F :=
          hActualBaseInFrontier ((hcontact 0).mpr rfl)
        exact Set.disjoint_left.mp disjoint_interior_frontier ha0I ha0front
      · exact hr₀out t (bot_lt_iff_ne_bot.mpr ht0) (interior_subset hyI)
    exact ⟨r₀,r₁,hr₀,hr₁,hr₀zero,hr₁zero,hr₀out,hr₁inside,
      hr₁off,hr₀trace,hr₁trace,hd⟩
  have hActualGenericRetainedClearOutwardExtendedConnectorStrip
      (c₀ : Curve S) (hc₀ : c₀.image⊆interior F)
      (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcontact : ∀ t,(a t).val∈boundaryCircle ↔ t=0)
      (hinside : ∀ t : Interval,0<t → (a t).val∈interior F)
      (hcircle : ∀ t,(a t).val∈c₀.image ↔ t=1)
      (hclear : ∀ t,(a t).val∉⋃ i,(c i).val.image) :
      ∃ (r : C(Interval,S)) (E : C(Interval × Set.Icc (-1 : ℝ) 1,S)),
        Topology.IsEmbedding r ∧ Topology.IsEmbedding E ∧ r 0∉F ∧
        (∀ t,E (t,⟨0,by norm_num⟩)=r t) ∧
        (∀ z,E z∉⋃ i,(c i).val.image) ∧
        (∀ t,(a t).val∈Set.range r) := by
    obtain ⟨r₀,r₁,hr₀,hr₁,hz₀,hz₁,ho,hi,_,ht₀,ht₁,hd⟩ :=
      hActualGenericTwoNegativeAccessContinuations c₀ hc₀ a ha hcontact hinside hcircle
    let G : Set S := ⋃ i,(c i).val.image
    have hGclosed : IsClosed G :=
      (isCompact_iUnion (fun i => isCompact_range (c i).val.embedded.continuous)).isClosed
    have hGfront : G⊆frontier F := by
      intro y hy
      rw [hfrontier]
      exact Or.inr hy
    obtain ⟨r,E,hr,hE,_,_,hrout,hcenter,hEclear,hrrange⟩ :=
      actual_extended_regional_connector_retained_clear_whole_strip
        F G hFclosed hGclosed hGfront a ha hclear r₀ r₁ hr₀ hr₁ hz₀ hz₁ ho hi ht₀ ht₁ hd
    refine ⟨r,E,hr,hE,hrout,hcenter,hEclear,?_⟩
    intro t
    rw [hrrange]
    exact Or.inl (Or.inr (Set.mem_range_self t))
  have hActualGenericMixedCleanConnectorActualRegionalRails
      (c₀ : Curve S) (hc₀ : c₀.image⊆interior F)
      (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcontact : ∀ t,(a t).val∈boundaryCircle ↔ t=0)
      (hinside : ∀ t : Interval,0<t → (a t).val∈interior F)
      (hcircle : ∀ t,(a t).val∈c₀.image ↔ t=1) :
      ∃ p₀ p₁ : C(Interval,↥F),
        Topology.IsEmbedding p₀ ∧ Topology.IsEmbedding p₁ ∧
        (p₀ 0).val∈boundaryCircle ∧ (p₁ 0).val∈boundaryCircle ∧
        (∀ t : Interval,0<t → (p₀ t).val∈interior F) ∧
        (∀ t : Interval,0<t → (p₁ t).val∈interior F) ∧
        (∀ t,(p₀ t).val∈c₀.image ↔ t=1) ∧
        (∀ t,(p₁ t).val∈c₀.image ↔ t=1) ∧
        Disjoint (Set.range (fun t => (p₀ t).val))
          (Set.range (fun t => (p₁ t).val)) := by
    let G : Set S := ⋃ i,(c i).val.image
    have hGclosed : IsClosed G :=
      (isCompact_iUnion (fun i => isCompact_range (c i).val.embedded.continuous)).isClosed
    have hGfront : G⊆frontier F := by
      intro y hy
      rw [hfrontier]
      exact Or.inr hy
    have hfront : frontier F⊆boundaryCircle∪G := by
      intro y hy
      rw [hfrontier] at hy
      exact hy
    have hclear : ∀ t,(a t).val∉G := by
      intro t hg
      by_cases ht : t=0
      · subst t
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hg
        exact Set.disjoint_left.mp (hbaseDisjoint i) hi ((hcontact 0).mpr rfl)
      · exact Set.disjoint_left.mp disjoint_interior_frontier
          (hinside t (bot_lt_iff_ne_bot.mpr ht)) (hGfront hg)
    obtain ⟨N₀,η₀,hp₀,hz₀,hη₀,_,ht₀,hl₀⟩ :=
      hActualGenericSuppliedConnectorHalfPlane a ha hcontact hinside
    obtain ⟨N₁,η₁,hp₁,hz₁,hη₁,_,ht₁,hl₁⟩ :=
      hActualSuppliedConnectorTerminalRayLine F c₀ hc₀ a ha hcircle
    exact actual_mixed_clean_connector_constructs_two_regional_proper_rails
      F boundaryCircle G c₀.image hFclosed
      (isCompact_range c₀.embedded.continuous).isClosed hGclosed hc₀ hGfront hfront a ha
      (hActualBaseInFrontier ((hcontact 0).mpr rfl)) hclear hcircle
      N₀ N₁ η₀ η₁ hp₀ hz₀ hη₀ ht₀ (fun y hy => (hl₀ y hy).2.2.1)
      hp₁ hz₁ hη₁ ht₁ hl₁
  have hActualInteriorEndpointBand (S : Type) [TopologicalSpace S] [T2Space S]
      (F B : Set S) (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcontact : ∀ t,(a t).val∈B ↔ t=0)
      (N : OpenPartialHomeomorph S Schoenflies.Plane) (η : ℝ)
      (hpN : (a 0).val∈N.source) (hN0 : N (a 0).val=0)
      (hη : 0<η) (htarget : Schoenflies.Plane.openSquare 0 η ⊆ N.target)
      (hlocal : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
        y∈interior F ∧
        (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
        (y∈B ↔ N y 0=0)) :
      ∃ b : ℝ,∃ hb : 0<b ∧ b<1,
      ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F),
        Topology.IsEmbedding E ∧
        (∀ t,E (t,⟨0,by norm_num⟩)=
          a ⟨b*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
        (∀ w,(E (0,w)).val∈B) ∧
        (∀ z,(E z).val∈interior F) ∧
        (∀ t : Interval,0<(t:ℝ) → ∀ w,(E (t,w)).val∉B) ∧
        (∀ z,E z∈Set.range a ↔ (z.2:ℝ)=0) ∧
        ∀ z,(E z).val∈N.symm '' Schoenflies.Plane.openSquare 0 η := by
    let O : Set S := N.symm '' (Schoenflies.Plane.openSquare 0 η ∩ {z : Schoenflies.Plane | z 0<0})
    let R : Set S := F \ O
    have hRsub : R ⊆ F := Set.sdiff_subset
    have haR : ∀ t,(a t).val∈R := by
      intro t
      refine ⟨(a t).property,?_⟩
      rintro ⟨z,hz,hza⟩
      have hW : (a t).val∈N.symm '' Schoenflies.Plane.openSquare 0 η := ⟨z,hz.1,hza⟩
      have hn : N (a t).val=z := by rw [←hza,N.right_inv (htarget hz.1)]
      have hpos := ((hlocal _ hW).2.1.mp (Set.mem_range_self t)).1
      rw [hn] at hpos
      exact (not_lt_of_ge hpos) hz.2
    let aR : C(Interval,↥R) := ⟨fun t => ⟨(a t).val,haR t⟩,
      (continuous_subtype_val.comp a.continuous).subtype_mk haR⟩
    have haRi : Topology.IsEmbedding aR := (aR.continuous.isClosedEmbedding (by
      intro t s he
      exact ha.injective (Subtype.ext (congrArg (fun u : ↥R => (u:S)) he)))).isEmbedding
    have hcontactR : ∀ t,(aR t).val∈B ↔ t=0 := hcontact
    have hhalf := hActualChartHalfRegion S F N η hη htarget (fun y hy => (hlocal y hy).1)
    have hlocalR : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
      (y∈Set.range (fun t => (aR t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
      (y∈B ↔ N y 0=0) ∧ (y∈R ↔ 0≤N y 0) ∧ (y∈interior R ↔ 0<N y 0) := by
      intro y hy
      exact ⟨(hlocal y hy).2.1,(hlocal y hy).2.2,(hhalf y hy).1,(hhalf y hy).2⟩
    obtain ⟨b,hb,ER,hER,hcenter,hbase,hinside,htrace,hchart⟩ :=
      actual_one_endpoint_regional_full_width_band R B aR haRi hcontactR N η hpN hN0 hη htarget hlocalR
    let E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F) :=
      ⟨fun z => ⟨(ER z).val,hRsub (ER z).property⟩,
        (continuous_subtype_val.comp ER.continuous).subtype_mk _⟩
    have hEi : Topology.IsEmbedding E := (E.continuous.isClosedEmbedding (by
      intro z w he
      exact hER.injective (Subtype.ext (congrArg (fun u : ↥F => (u:S)) he)))).isEmbedding
    refine ⟨b,hb,E,hEi,?_,hbase,?_,?_,?_,hchart⟩
    · intro t
      apply Subtype.ext
      exact congrArg (fun u : ↥R => (u:S)) (hcenter t)
    · intro z
      exact (hlocal _ (hchart z)).1
    · intro t ht w
      exact (hinside t ht w).2
    · intro z
      rw [←htrace]
      constructor
      · rintro ⟨t,ht⟩
        exact ⟨t,Subtype.ext (congrArg (fun u : ↥F => (u:S)) ht)⟩
      · rintro ⟨t,ht⟩
        exact ⟨t,Subtype.ext (congrArg (fun u : ↥R => (u:S)) ht)⟩
  have hActualSuppliedConnectorTerminalBand (F : Set S)
      (c : Curve S) (hc : c.image ⊆ interior F)
      (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
      (hcircle : ∀ t,(a t).val∈c.image ↔ t=1) :
      ∃ (N : OpenPartialHomeomorph S Schoenflies.Plane) (η b : ℝ)
        (hb : 0<b ∧ b<1) (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F)),
        0<η ∧ Schoenflies.Plane.openSquare 0 η ⊆ N.target ∧
        (∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
          y∈interior F ∧
          (y∈Set.range (fun t => (a t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
          (y∈c.image ↔ N y 0=0)) ∧
        Topology.IsEmbedding E ∧
        (∀ t,E (t,⟨0,by norm_num⟩)=
          a ⟨1-b*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
        (∀ w,(E (0,w)).val∈c.image) ∧ (∀ z,(E z).val∈interior F) ∧
        (∀ t : Interval,0<(t:ℝ) → ∀ w,(E (t,w)).val∉c.image) ∧
        (∀ z,E z∈Set.range a ↔ (z.2:ℝ)=0) ∧
        ∀ z,(E z).val∈N.symm '' Schoenflies.Plane.openSquare 0 η := by
    let ρ : C(Interval,Interval) := ⟨unitInterval.symm,unitInterval.continuous_symm⟩
    have hρ : Topology.IsEmbedding ρ :=
      (ρ.continuous.isClosedEmbedding unitInterval.symm_involutive.injective).isEmbedding
    let rev : C(Interval,↥F) := a.comp ρ
    have hrev : Topology.IsEmbedding rev := ha.comp hρ
    have hrev0 : (rev 0).val=(a 1).val := by simp [rev,ρ]
    have hcontact : ∀ t,(rev t).val∈c.image ↔ t=0 := by
      intro t
      change (a (unitInterval.symm t)).val∈c.image ↔ t=0
      rw [hcircle]
      constructor
      · intro he
        apply Subtype.ext
        have hv := congrArg Subtype.val he
        change 1-(t:ℝ)=1 at hv
        change (t:ℝ)=0
        linarith
      · rintro rfl
        simp
    have htrace : Set.range (fun t => (rev t).val)=Set.range (fun t => (a t).val) := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨unitInterval.symm t,?_⟩
        change (a (unitInterval.symm (unitInterval.symm t))).val=(a t).val
        rw [unitInterval.symm_involutive t]
    obtain ⟨N,η,hpN,hN0,hη,hη1,hηtarget,hlocal⟩ :=
      hActualSuppliedConnectorTerminalRayLine F c hc a ha hcircle
    have hlocalRev : ∀ y∈N.symm '' Schoenflies.Plane.openSquare 0 η,
        y∈interior F ∧
        (y∈Set.range (fun t => (rev t).val) ↔ 0≤N y 0 ∧ N y 1=0) ∧
        (y∈c.image ↔ N y 0=0) := by simpa only [htrace] using hlocal
    obtain ⟨b,hb,E,hE,hcenter,hbase,hinside,havoid,hzero,hchart⟩ :=
      hActualInteriorEndpointBand S F c.image rev hrev hcontact N η
        (hrev0.symm ▸ hpN) (by rw [hrev0];exact hN0) hη hηtarget hlocalRev
    have htraceSubtype : Set.range rev=Set.range a := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,rfl⟩
      · rintro ⟨t,rfl⟩
        refine ⟨unitInterval.symm t,?_⟩
        change a (unitInterval.symm (unitInterval.symm t))=a t
        rw [unitInterval.symm_involutive t]
    refine ⟨N,η,b,hb,E,hη,hηtarget,hlocal,hE,?_,hbase,hinside,havoid,?_,hchart⟩
    · intro t
      rw [hcenter]
      change a (unitInterval.symm ⟨b*(t:ℝ),_⟩)=a ⟨1-b*(t:ℝ),_⟩
      exact congrArg a (Subtype.ext rfl)
    · simpa only [htraceSubtype] using hzero
  have hActualEndpointBandTrim {X : Type} [TopologicalSpace X] [T2Space X]
      (E : C(Interval × Set.Icc (-1 : ℝ) 1,X)) (hE : Topology.IsEmbedding E)
      (U : Set X) (hU : IsOpen U)
      (hcore : ∀ t : Interval,E (⟨(t:ℝ)/4,by constructor <;> nlinarith [t.property.1,t.property.2]⟩,
        ⟨0,by norm_num⟩)∈U) :
      ∃ (δ : ℝ) (hδ : 0<δ ∧ δ<1)
        (T : C(Interval × Set.Icc (-1 : ℝ) 1,X)),
        Topology.IsEmbedding T ∧ Set.range T ⊆ U ∧
        ∀ z,T z=E (⟨(z.1:ℝ)/4,by constructor <;> nlinarith [z.1.property.1,z.1.property.2]⟩,
          ⟨δ*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩) := by
    let f : Interval → Interval := fun t => ⟨(t:ℝ)/4,by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩
    have hf : Continuous f := (continuous_subtype_val.div_const 4).subtype_mk _
    let E' : C(Interval × Set.Icc (-1 : ℝ) 1,X) :=
      ⟨fun z => E (f z.1,z.2),E.continuous.comp ((hf.comp continuous_fst).prodMk continuous_snd)⟩
    have hprod : (Set.univ : Set Interval) ×ˢ ({⟨0,by norm_num⟩} : Set (Set.Icc (-1 : ℝ) 1)) ⊆ E' ⁻¹' U := by
      rintro ⟨t,w⟩ ⟨ht,hw⟩
      have hw0 : w=⟨0,by norm_num⟩ := hw
      subst w
      exact hcore t
    obtain ⟨V,W,hV,hW,hall,hzero,hVW⟩ := generalized_tube_lemma
      isCompact_univ isCompact_singleton (hU.preimage E'.continuous) hprod
    obtain ⟨ε,hε,hεW⟩ := Metric.isOpen_iff.mp hW _ (hzero (Set.mem_singleton _))
    let δ := min (ε/2) (1/2)
    have hδ : 0<δ ∧ δ<1 := by
      refine ⟨lt_min (by positivity) (by norm_num),?_⟩
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hδε : δ<ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let k : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1 := fun w => ⟨δ*(w:ℝ),by
      constructor <;> nlinarith [w.property.1,w.property.2,hδ.1,hδ.2]⟩
    have hk : Continuous k := (continuous_const.mul continuous_subtype_val).subtype_mk _
    let T : C(Interval × Set.Icc (-1 : ℝ) 1,X) :=
      ⟨fun z => E (f z.1,k z.2),E.continuous.comp ((hf.comp continuous_fst).prodMk (hk.comp continuous_snd))⟩
    have hinj : Function.Injective T := by
      intro z v hzv
      have he := hE.injective hzv
      have he0 := congrArg (fun p : Interval × Set.Icc (-1 : ℝ) 1 => (p.1:ℝ)) he
      have he1 := congrArg (fun p : Interval × Set.Icc (-1 : ℝ) 1 => (p.2:ℝ)) he
      dsimp [f,k] at he0 he1
      apply Prod.ext <;> apply Subtype.ext
      · linarith
      · nlinarith [hδ.1]
    refine ⟨δ,hδ,T,(T.continuous.isClosedEmbedding hinj).isEmbedding,?_,fun z => rfl⟩
    rintro y ⟨z,rfl⟩
    change E' (z.1,k z.2)∈U
    apply hVW
    refine ⟨hall (Set.mem_univ _),hεW ?_⟩
    change dist (δ*(z.2:ℝ)) (0:ℝ)<ε
    rw [Real.dist_eq,sub_zero]
    have hw : |(z.2:ℝ)|≤1 := abs_le.mpr z.2.property
    rw [abs_mul,abs_of_pos hδ.1]
    exact lt_of_le_of_lt (by nlinarith) hδε
  have hActualTwoEndpointBandsSeparateAvoid {X : Type} [TopologicalSpace X] [T2Space X]
      (a : C(Interval,X)) (ha : Topology.IsEmbedding a)
      (b0 b1 : ℝ) (hb0 : 0<b0 ∧ b0<1) (hb1 : 0<b1 ∧ b1<1)
      (B0 B1 : Set X) (hB0 : IsClosed B0) (hB1 : IsClosed B1)
      (ha0 : ∀ t,a t∈B0 ↔ t=0) (ha1 : ∀ t,a t∈B1 ↔ t=1)
      (E0 E1 : C(Interval × Set.Icc (-1 : ℝ) 1,X))
      (hE0 : Topology.IsEmbedding E0) (hE1 : Topology.IsEmbedding E1)
      (hc0 : ∀ t,E0 (t,⟨0,by norm_num⟩)=a ⟨b0*(t:ℝ),by
        constructor <;> nlinarith [t.property.1,t.property.2,hb0.1,hb0.2]⟩)
      (hc1 : ∀ t,E1 (t,⟨0,by norm_num⟩)=a ⟨1-b1*(t:ℝ),by
        constructor <;> nlinarith [t.property.1,t.property.2,hb1.1,hb1.2]⟩) :
      ∃ (δ0 δ1 : ℝ) (hδ0 : 0<δ0 ∧ δ0<1) (hδ1 : 0<δ1 ∧ δ1<1)
        (T0 T1 : C(Interval × Set.Icc (-1 : ℝ) 1,X)),
        Topology.IsEmbedding T0 ∧ Topology.IsEmbedding T1 ∧
        Disjoint (Set.range T0) (Set.range T1) ∧
        Disjoint (Set.range T0) B1 ∧ Disjoint (Set.range T1) B0 ∧
        (∀ z,T0 z=E0 (⟨(z.1:ℝ)/4,by constructor <;> nlinarith [z.1.property.1,z.1.property.2]⟩,
          ⟨δ0*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ0.1,hδ0.2]⟩)) ∧
        (∀ z,T1 z=E1 (⟨(z.1:ℝ)/4,by constructor <;> nlinarith [z.1.property.1,z.1.property.2]⟩,
          ⟨δ1*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ1.1,hδ1.2]⟩)) := by
    let f : Interval → Interval := fun t => ⟨(t:ℝ)/4,by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩
    have hf : Continuous f := (continuous_subtype_val.div_const 4).subtype_mk _
    let c0 : C(Interval,X) := ⟨fun t => E0 (f t,⟨0,by norm_num⟩),
      E0.continuous.comp (hf.prodMk continuous_const)⟩
    let c1 : C(Interval,X) := ⟨fun t => E1 (f t,⟨0,by norm_num⟩),
      E1.continuous.comp (hf.prodMk continuous_const)⟩
    have hdisj : Disjoint (Set.range c0) (Set.range c1) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨t,rfl⟩ ⟨s,hs⟩
      have he : E0 (f t,⟨0,by norm_num⟩)=E1 (f s,⟨0,by norm_num⟩) := hs.symm
      rw [hc0,hc1] at he
      have hv := congrArg (fun q : Interval => (q:ℝ)) (ha.injective he)
      dsimp [f] at hv
      nlinarith [t.property.1,t.property.2,s.property.1,s.property.2,hb0.1,hb0.2,hb1.1,hb1.2]
    obtain ⟨U,V,hU,hV,hcU,hcV,hUV⟩ := SeparatedNhds.of_isCompact_isCompact
      (isCompact_range c0.continuous) (isCompact_range c1.continuous) hdisj
    have hclear0 (t : Interval) : c0 t∉B1 := by
      change E0 (f t,⟨0,by norm_num⟩)∉B1
      rw [hc0,ha1]
      intro he
      have hv := congrArg (fun q : Interval => (q:ℝ)) he
      dsimp [f] at hv
      norm_num at hv
      nlinarith [t.property.1,t.property.2,hb0.1,hb0.2]
    have hclear1 (t : Interval) : c1 t∉B0 := by
      change E1 (f t,⟨0,by norm_num⟩)∉B0
      rw [hc1,ha0]
      intro he
      have hv := congrArg (fun q : Interval => (q:ℝ)) he
      dsimp [f] at hv
      norm_num at hv
      nlinarith [t.property.1,t.property.2,hb1.1,hb1.2]
    obtain ⟨δ0,hδ0,T0,hT0,hTU,hT0eq⟩ := hActualEndpointBandTrim E0 hE0 (U∩B1ᶜ)
      (hU.inter hB1.isOpen_compl) (fun t => ⟨hcU (Set.mem_range_self t),hclear0 t⟩)
    obtain ⟨δ1,hδ1,T1,hT1,hTV,hT1eq⟩ := hActualEndpointBandTrim E1 hE1 (V∩B0ᶜ)
      (hV.inter hB0.isOpen_compl) (fun t => ⟨hcV (Set.mem_range_self t),hclear1 t⟩)
    exact ⟨δ0,δ1,hδ0,hδ1,T0,T1,hT0,hT1,
      hUV.mono (hTU.trans Set.inter_subset_left) (hTV.trans Set.inter_subset_left),
      Set.disjoint_left.mpr (fun y hy hn => (hTU hy).2 hn),
      Set.disjoint_left.mpr (fun y hy hn => (hTV hy).2 hn),hT0eq,hT1eq⟩
  have hActualGenericCoherentSeparatedEndpointBands (j : J) :
      ∃ (b : EssentialCurve S) (a : C(Interval,↥F)),Topology.IsEmbedding a ∧
        b.val.image⊆interior F ∧
        Quotient.mk (essentialCurveSetoid S) b=Quotient.mk (essentialCurveSetoid S) (c j) ∧
        (∀ t,(a t).val∈boundaryCircle ↔ t=0) ∧
        (∀ t,(a t).val∈b.val.image ↔ t=1) ∧
        (∀ t : Interval,0<(t:ℝ) → (a t).val∈interior F) ∧
        ∃ (α0 α1 : ℝ) (hα0 : 0<α0 ∧ α0<1/4) (hα1 : 0<α1 ∧ α1<1/4)
          (T0 T1 : C(Interval × Set.Icc (-1:ℝ) 1,↥F)),
          Topology.IsEmbedding T0 ∧ Topology.IsEmbedding T1 ∧
          Disjoint (Set.range T0) (Set.range T1) ∧
          (∀ z,(T0 z).val∉b.val.image) ∧ (∀ z,(T1 z).val∉boundaryCircle) ∧
          (∀ t,T0 (t,⟨0,by norm_num⟩)=a ⟨α0*(t:ℝ),by
            constructor <;> nlinarith [t.property.1,t.property.2,hα0.1,hα0.2]⟩) ∧
          (∀ t,T1 (t,⟨0,by norm_num⟩)=a ⟨1-α1*(t:ℝ),by
            constructor <;> nlinarith [t.property.1,t.property.2,hα1.1,hα1.2]⟩) ∧
          (∀ w,(T0 (0,w)).val∈boundaryCircle) ∧ (∀ w,(T1 (0,w)).val∈b.val.image) ∧
          (∀ t : Interval,0<(t:ℝ) → ∀ w,
            (T0 (t,w)).val∈interior F ∧ (T0 (t,w)).val∉boundaryCircle) ∧
          (∀ z,(T1 z).val∈interior F) ∧
          (∀ t : Interval,0<(t:ℝ) → ∀ w,(T1 (t,w)).val∉b.val.image) ∧
          (∀ z,T0 z∈Set.range a ↔ (z.2:ℝ)=0) ∧
          (∀ z,T1 z∈Set.range a ↔ (z.2:ℝ)=0) := by
    obtain ⟨b,a,ha,hc,hclass,hbase,hcircle,hfrontier,hends,hinside⟩ :=
      hActualGenericEssentialCircleEmbeddedCleanAccess j
    have hcontact : ∀ t,(a t).val∈boundaryCircle ↔ t=0 := fun t =>
      ⟨fun ht => (hfrontier t).mp (hActualBaseInFrontier ht),fun ht => ht.symm ▸ hbase⟩
    obtain ⟨b0,hb0,E0,hE0,hc0,hend0,hi0,htrace0⟩ :=
      hActualGenericSuppliedConnectorInitialBand a ha hcontact hinside
    obtain ⟨N,η,b1,hb1,E1,hη,hηt,hlocal,hE1,hc1,hend1,hi1,hav1,htrace1,hchart⟩ :=
      hActualSuppliedConnectorTerminalBand F b.val hc a ha hcircle
    have hB : IsClosed boundaryCircle := by
      exact ((isCompact_sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R).image_of_continuousOn
        ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.continuousOn.mono
          (Metric.sphere_subset_closedBall.trans htarget))).isClosed
    have hC : IsClosed b.val.image := (isCompact_range b.val.embedded.continuous).isClosed
    obtain ⟨δ0,δ1,hδ0,hδ1,T0,T1,hT0,hT1,hdisj,hclear0,hclear1,he0,he1⟩ :=
      hActualTwoEndpointBandsSeparateAvoid a ha b0 b1 hb0 hb1
        (Subtype.val ⁻¹' boundaryCircle) (Subtype.val ⁻¹' b.val.image)
        (hB.preimage continuous_subtype_val) (hC.preimage continuous_subtype_val)
        hcontact hcircle E0 E1 hE0 hE1 hc0 hc1
    let α0 := b0/4
    let α1 := b1/4
    have hα0 : 0<α0 ∧ α0<1/4 := by dsimp [α0];constructor <;> linarith [hb0.1,hb0.2]
    have hα1 : 0<α1 ∧ α1<1/4 := by dsimp [α1];constructor <;> linarith [hb1.1,hb1.2]
    refine ⟨b,a,ha,hc,hclass,hcontact,hcircle,hinside,α0,α1,hα0,hα1,T0,T1,hT0,hT1,hdisj,
      fun z => Set.disjoint_left.mp hclear0 (Set.mem_range_self z),
      fun z => Set.disjoint_left.mp hclear1 (Set.mem_range_self z),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro t
      rw [he0]
      have hw : (⟨δ0*0,by constructor <;> nlinarith [hδ0.1,hδ0.2]⟩ : Set.Icc (-1:ℝ) 1)=⟨0,by norm_num⟩ := Subtype.ext (mul_zero _)
      rw [hw,hc0]
      apply congrArg a
      apply Subtype.ext
      change b0*((t:ℝ)/4)=(b0/4)*(t:ℝ)
      ring
    · intro t
      rw [he1]
      have hw : (⟨δ1*0,by constructor <;> nlinarith [hδ1.1,hδ1.2]⟩ : Set.Icc (-1:ℝ) 1)=⟨0,by norm_num⟩ := Subtype.ext (mul_zero _)
      rw [hw,hc1]
      apply congrArg a
      apply Subtype.ext
      change 1-b1*((t:ℝ)/4)=1-(b1/4)*(t:ℝ)
      ring
    · intro w
      rw [he0]
      change (E0 (⟨(0:ℝ)/4,by norm_num⟩,⟨δ0*(w:ℝ),by
        constructor <;> nlinarith [w.property.1,w.property.2,hδ0.1,hδ0.2]⟩)).val∈boundaryCircle
      have ht : (⟨(0:ℝ)/4,by norm_num⟩ : Interval)=0 := Subtype.ext (by norm_num)
      rw [ht]
      exact hend0 _
    · intro w
      rw [he1]
      change (E1 (⟨(0:ℝ)/4,by norm_num⟩,⟨δ1*(w:ℝ),by
        constructor <;> nlinarith [w.property.1,w.property.2,hδ1.1,hδ1.2]⟩)).val∈b.val.image
      have ht : (⟨(0:ℝ)/4,by norm_num⟩ : Interval)=0 := Subtype.ext (by norm_num)
      rw [ht]
      exact hend1 _
    · intro t ht w
      rw [he0]
      exact hi0 _ (div_pos ht (by norm_num)) _
    · intro z
      rw [he1]
      exact hi1 _
    · intro t ht w
      rw [he1]
      exact hav1 _ (div_pos ht (by norm_num)) _
    · intro z
      rw [he0,htrace0]
      change δ0*(z.2:ℝ)=0 ↔ (z.2:ℝ)=0
      simp [hδ0.1.ne']
    · intro z
      rw [he1,htrace1]
      change δ1*(z.2:ℝ)=0 ↔ (z.2:ℝ)=0
      simp [hδ1.1.ne']
  have hActualEssentialCircleNonNull (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
      (c : EssentialCurve S) : ¬ (⟨c.val.map,c.val.embedded.continuous⟩ : C(Circle,S)).Nullhomotopic := by
    intro hcnull
    let u := c.val.map (1 : Circle)
    let U := Σ y : S,Path.Homotopic.Quotient u y
    obtain ⟨t,hCover⟩ := CurveComplex.LocalSurgery.closed_surface_actual_second_countable_universal_cover u
    letI : TopologicalSpace U := t
    rcases hCover with ⟨hSC,hT2,hChart,hSimply,hQuot,hSurj,hLift⟩
    letI : SecondCountableTopology U := hSC
    letI : T2Space U := hT2
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) U := hChart.some
    letI : SimplyConnectedSpace U := hSimply
    let p : U → S := Sigma.fst
    have hModel : Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ U) ∨
        Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₜ U) :=
      CurveComplex.LocalSurgery.closed_surface_simply_connected_cover_plane_or_sphere p hQuot.isCoveringMap hSurj
    apply c.property
    rcases hModel with hPlane | hSphere
    · obtain ⟨e⟩ := hPlane
      obtain ⟨action,hq⟩ := CurveComplex.LocalSurgery.actual_quotient_cover_domain_homeomorph_transport p hQuot e
      letI := action
      exact CurveComplex.boundsDisc_of_nullhomotopic_planar_quotient_cover_complete (p ∘ e) hq c.val hcnull
    · obtain ⟨e⟩ := hSphere
      obtain ⟨action,hq⟩ := CurveComplex.LocalSurgery.actual_quotient_cover_domain_homeomorph_transport p hQuot e
      letI := action
      exact CurveComplex.LocalSurgery.boundsDisc_of_nullhomotopic_spherical_quotient_cover_complete (p ∘ e) hq c.val hcnull
  have hActualHomotopicTwoArcsNullCircle {S : Type} [TopologicalSpace S] [T2Space S]
      {u z : S} (f g : Path u z) (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g)
      (hinter : Set.range f ∩ Set.range g={u,z}) (hhom : f.Homotopic g) :
      ∃ c : Curve S,c.image=Set.range f ∪ Set.range g ∧
        (⟨c.map,c.embedded.continuous⟩ : C(Circle,S)).Nullhomotopic := by
    have hmeet : ∀ s t,f s=g t → (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
      intro s t he
      have hm : f s∈({u,z} : Set S) := hinter ▸ ⟨Set.mem_range_self s,⟨t,he.symm⟩⟩
      rcases Set.mem_insert_iff.mp hm with hu | hz
      · left
        exact ⟨hf.injective (hu.trans f.source.symm),
          hg.injective (he.symm.trans (hu.trans g.source.symm))⟩
      · have hz' : f s=z := Set.mem_singleton_iff.mp hz
        right
        exact ⟨hf.injective (hz'.trans f.target.symm),
          hg.injective (he.symm.trans (hz'.trans g.target.symm))⟩
    have hnull : (f.trans g.symm).Homotopic (Path.refl u) :=
      (hhom.hcomp (Path.Homotopic.refl g.symm)).trans (Path.Homotopic.trans_symm g)
    have hloopCollision : ∀ s t, (f.trans g.symm) s = (f.trans g.symm) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
      intro s t h
      simp only [Path.trans_apply, Path.symm_apply] at h
      split_ifs at h with hs ht ht
      · left
        have he := congrArg Subtype.val (hf.injective h)
        apply Subtype.ext
        dsimp at he
        linarith
      · have he := hmeet _ _ h
        rcases he with ⟨hs0, ht0⟩ | ⟨hs1, ht1⟩
        · right; left
          constructor <;> apply Subtype.ext
          · change (s : ℝ) = 0
            have := congrArg Subtype.val hs0; dsimp at this; linarith
          · change (t : ℝ) = 1
            have := congrArg Subtype.val ht0
            simp only [unitInterval.coe_symm_eq] at this
            dsimp at this; linarith
        · exfalso
          have := congrArg Subtype.val ht1
          simp only [unitInterval.coe_symm_eq] at this
          dsimp at this; linarith
      · have he := hmeet _ _ h.symm
        rcases he with ⟨ht0, hs0⟩ | ⟨ht1, hs1⟩
        · right; right
          constructor <;> apply Subtype.ext
          · change (s : ℝ) = 1
            have := congrArg Subtype.val hs0
            simp only [unitInterval.coe_symm_eq] at this
            dsimp at this; linarith
          · change (t : ℝ) = 0
            have := congrArg Subtype.val ht0; dsimp at this; linarith
        · exfalso
          have := congrArg Subtype.val hs1
          simp only [unitInterval.coe_symm_eq] at this
          dsimp at this; linarith
      · left
        have he := congrArg Subtype.val (hg.injective h)
        apply Subtype.ext
        simp only [unitInterval.coe_symm_eq] at he
        linarith
    obtain ⟨c,hc,hcn⟩ :=
      CurveComplex.LocalSurgery.nullhomotopic_loop_with_only_endpoint_collision_gives_curve u
        (f.trans g.symm) hloopCollision hnull
    refine ⟨c,?_,hcn⟩
    simpa only [Path.trans_range, Path.symm_range] using hc
  have hActualComplementaryEssentialCircleArcsNonhomotopic
      (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
      (c : EssentialCurve S) {u z : S} (f g : Path u z)
      (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g)
      (hinter : Set.range f ∩ Set.range g={u,z})
      (hcover : Set.range f ∪ Set.range g=c.val.image) : ¬ f.Homotopic g := by
    intro hh
    obtain ⟨c',himage,hnull⟩ := hActualHomotopicTwoArcsNullCircle f g hf hg hinter hh
    have hsame : c'.image=c.val.image := himage.trans hcover
    have he : Essential c' := by
      rintro ⟨d,hd,hboundary⟩
      exact c.property ⟨d,hd,hboundary.trans hsame⟩
    exact hActualEssentialCircleNonNull S ⟨c',he⟩ hnull
  have hActualEmbeddedDiskPathsHomotopic {X : Type} [TopologicalSpace X]
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,X))
      (hd : Topology.IsEmbedding d) {x y : X} (p q : Path x y)
      (hp : Set.range p ⊆ Set.range d) (hq : Set.range q ⊆ Set.range d) :
      p.Homotopic q := by
    letI : ContractibleSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      (convex_closedBall _ _).contractibleSpace ⟨0,by simp⟩
    letI : ContractibleSpace (Set.range d) := hd.toHomeomorph.symm.contractibleSpace
    have hx : x∈Set.range d := p.source ▸ hp (Set.mem_range_self 0)
    have hy : y∈Set.range d := p.target ▸ hp (Set.mem_range_self 1)
    let xr : Set.range d := ⟨x,hx⟩
    let yr : Set.range d := ⟨y,hy⟩
    let P : Path xr yr := ⟨⟨fun t => ⟨p t,hp (Set.mem_range_self t)⟩,
      p.continuous.subtype_mk _⟩,Subtype.ext p.source,Subtype.ext p.target⟩
    let Q : Path xr yr := ⟨⟨fun t => ⟨q t,hq (Set.mem_range_self t)⟩,
      q.continuous.subtype_mk _⟩,Subtype.ext q.source,Subtype.ext q.target⟩
    have hPQ := SimplyConnectedSpace.paths_homotopic P Q
    exact hPQ.map (⟨Subtype.val,continuous_subtype_val⟩ : C(Set.range d,X))
  have hActualBoundaryDiskWitnessHomotopy {X : Type} [TopologicalSpace X]
      (a b : C(Interval,X)) (h0 : b 0=a 0) (h1 : b 1=a 1)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,X))
      (hd : Topology.IsEmbedding d)
      (hboundary : d '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range a ∪ Set.range b) :
      let p : Path (a 0) (a 1) := ⟨a,rfl,rfl⟩
      let q : Path (a 0) (a 1) := ⟨b,h0,h1⟩
      p.Homotopic q := by
    dsimp only
    apply hActualEmbeddedDiskPathsHomotopic d hd
    · intro y hy
      have hh : y∈d '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
        hboundary.symm ▸ Or.inl hy
      exact Set.image_subset_range _ _ hh
    · intro y hy
      have hh : y∈d '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
        hboundary.symm ▸ Or.inr hy
      exact Set.image_subset_range _ _ hh
  have hActualChartClosedDiskPathsHomotopic {X : Type} [TopologicalSpace X] [T2Space X]
      (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 2)))
      (center : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hR : 0<R)
      (htarget : Metric.closedBall center R ⊆ e.target)
      {x y : X} (p q : Path x y)
      (hp : Set.range p ⊆ e.symm '' Metric.closedBall center R)
      (hq : Set.range q ⊆ e.symm '' Metric.closedBall center R) : p.Homotopic q := by
    let D := Metric.closedBall center R
    letI : ContractibleSpace D := (convex_closedBall _ _).contractibleSpace
      ⟨center,by simp [D,hR.le]⟩
    let d : C(D,X) := ⟨fun z => e.symm z.val,
      e.symm.continuousOn.comp_continuous continuous_subtype_val (fun z => htarget z.property)⟩
    have hd : Topology.IsEmbedding d := by
      apply (d.continuous.isClosedEmbedding _).isEmbedding
      intro z w hzw
      exact Subtype.ext (e.symm.injOn (htarget z.property) (htarget w.property) hzw)
    have hD : Set.range d=e.symm '' Metric.closedBall center R := by
      ext z
      constructor
      · rintro ⟨u,rfl⟩
        exact ⟨u.val,u.property,rfl⟩
      · rintro ⟨u,hu,rfl⟩
        exact ⟨⟨u,hu⟩,rfl⟩
    letI : ContractibleSpace (Set.range d) := hd.toHomeomorph.symm.contractibleSpace
    have hx : x∈Set.range d := hD.symm ▸ (p.source ▸ hp (Set.mem_range_self 0))
    have hy : y∈Set.range d := hD.symm ▸ (p.target ▸ hp (Set.mem_range_self 1))
    let xr : Set.range d := ⟨x,hx⟩
    let yr : Set.range d := ⟨y,hy⟩
    have hpD (t) : p t∈Set.range d := hD.symm ▸ hp (Set.mem_range_self t)
    have hqD (t) : q t∈Set.range d := hD.symm ▸ hq (Set.mem_range_self t)
    let P : Path xr yr := ⟨⟨fun t => ⟨p t,hpD t⟩,p.continuous.subtype_mk _⟩,
      Subtype.ext p.source,Subtype.ext p.target⟩
    let Q : Path xr yr := ⟨⟨fun t => ⟨q t,hqD t⟩,q.continuous.subtype_mk _⟩,
      Subtype.ext q.source,Subtype.ext q.target⟩
    exact (SimplyConnectedSpace.paths_homotopic P Q).map
      (⟨Subtype.val,continuous_subtype_val⟩ : C(Set.range d,X))
  have hActualFullBandBoundaryPathRelation {X : Type} [TopologicalSpace X]
      (E : C(Interval × Set.Icc (-1 : ℝ) 1,X)) :
      ∃ (p : Path (E (0,⟨1,by norm_num⟩)) (E (1,⟨1,by norm_num⟩)))
        (q : Path (E (0,⟨-1,by norm_num⟩)) (E (1,⟨-1,by norm_num⟩)))
        (b0 : Path (E (0,⟨1,by norm_num⟩)) (E (0,⟨-1,by norm_num⟩)))
        (b1 : Path (E (1,⟨1,by norm_num⟩)) (E (1,⟨-1,by norm_num⟩))),
        (∀ t,p t=E (t,⟨1,by norm_num⟩)) ∧
        (∀ t,q t=E (t,⟨-1,by norm_num⟩)) ∧
        (∀ t,b0 t=E (0,⟨1-2*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩)) ∧
        (∀ t,b1 t=E (1,⟨1-2*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩)) ∧
        (p.trans b1).Homotopic (b0.trans q) := by
    letI : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    letI : ContractibleSpace (Set.Icc (-1 : ℝ) 1) :=
      (convex_Icc (-1:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    let p : Path ((0:Interval),(⟨1,by norm_num⟩ : Set.Icc (-1:ℝ) 1))
        ((1:Interval),(⟨1,by norm_num⟩ : Set.Icc (-1:ℝ) 1)) :=
      ⟨⟨fun t => (t,⟨1,by norm_num⟩),continuous_id.prodMk continuous_const⟩,rfl,rfl⟩
    let q : Path ((0:Interval),(⟨-1,by norm_num⟩ : Set.Icc (-1:ℝ) 1))
        ((1:Interval),(⟨-1,by norm_num⟩ : Set.Icc (-1:ℝ) 1)) :=
      ⟨⟨fun t => (t,⟨-1,by norm_num⟩),continuous_id.prodMk continuous_const⟩,rfl,rfl⟩
    let k : C(Interval,Set.Icc (-1:ℝ) 1) := ⟨fun t => ⟨1-2*(t:ℝ),by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩,
      by fun_prop⟩
    let b0 : Path ((0:Interval),(⟨1,by norm_num⟩ : Set.Icc (-1:ℝ) 1))
        ((0:Interval),(⟨-1,by norm_num⟩ : Set.Icc (-1:ℝ) 1)) :=
      ⟨⟨fun t => (0,k t),continuous_const.prodMk k.continuous⟩,
        Prod.ext rfl (Subtype.ext (by norm_num [k])),Prod.ext rfl (Subtype.ext (by norm_num [k]))⟩
    let b1 : Path ((1:Interval),(⟨1,by norm_num⟩ : Set.Icc (-1:ℝ) 1))
        ((1:Interval),(⟨-1,by norm_num⟩ : Set.Icc (-1:ℝ) 1)) :=
      ⟨⟨fun t => (1,k t),continuous_const.prodMk k.continuous⟩,
        Prod.ext rfl (Subtype.ext (by norm_num [k])),Prod.ext rfl (Subtype.ext (by norm_num [k]))⟩
    refine ⟨p.map E.continuous,q.map E.continuous,b0.map E.continuous,b1.map E.continuous,
      fun t => rfl,fun t => rfl,fun t => rfl,fun t => rfl,?_⟩
    have hh := (SimplyConnectedSpace.paths_homotopic (p.trans b1) (b0.trans q)).map E
    simpa only [Path.map_trans] using hh
  have hActualBandDiskTerminalLoopNull {X : Type} [TopologicalSpace X]
      {x0 y0 x1 y1 : X} (p : Path x0 x1) (q : Path y0 y1)
      (b0 : Path x0 y0) (b1 d : Path x1 y1)
      (hband : (p.trans b1).Homotopic (b0.trans q))
      (hdisk : ((p.trans d).trans q.symm).Homotopic b0) :
      d.Homotopic b1 ∧ (d.trans b1.symm).Homotopic (Path.refl x1) := by
    have hcollapse : (((p.trans d).trans q.symm).trans q).Homotopic (p.trans d) :=
      (Path.Homotopic.trans_assoc (p.trans d) q.symm q).trans
        (((Path.Homotopic.refl (p.trans d)).hcomp (Path.Homotopic.symm_trans q)).trans
          (Path.Homotopic.trans_refl (p.trans d)))
    have hpd : (p.trans d).Homotopic (p.trans b1) :=
      (hcollapse.symm.trans (hdisk.hcomp (Path.Homotopic.refl q))).trans hband.symm
    have hpre := (Path.Homotopic.refl p.symm).hcomp hpd
    have hleft : (p.symm.trans (p.trans d)).Homotopic d :=
      (Path.Homotopic.trans_assoc p.symm p d).symm.trans
        (((Path.Homotopic.symm_trans p).hcomp (Path.Homotopic.refl d)).trans
          (Path.Homotopic.refl_trans d))
    have hright : (p.symm.trans (p.trans b1)).Homotopic b1 :=
      (Path.Homotopic.trans_assoc p.symm p b1).symm.trans
        (((Path.Homotopic.symm_trans p).hcomp (Path.Homotopic.refl b1)).trans
          (Path.Homotopic.refl_trans b1))
    have hdb := (hleft.symm.trans hpre).trans hright
    exact ⟨hdb,(hdb.hcomp (Path.Homotopic.refl b1.symm)).trans (Path.Homotopic.trans_symm b1)⟩
  have hActualBandDiskEssentialCircleContradiction (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
      (c : EssentialCurve S) {x0 y0 x1 y1 : S}
      (p : Path x0 x1) (q : Path y0 y1) (b0 : Path x0 y0) (b1 d : Path x1 y1)
      (hb1 : Topology.IsEmbedding b1) (hd : Topology.IsEmbedding d)
      (hinter : Set.range d ∩ Set.range b1={x1,y1})
      (hcover : Set.range d ∪ Set.range b1=c.val.image)
      (hband : (p.trans b1).Homotopic (b0.trans q)) :
      ¬ ((p.trans d).trans q.symm).Homotopic b0 := by
    intro hdisk
    have hterminal := (hActualBandDiskTerminalLoopNull p q b0 b1 d hband hdisk).1
    exact hActualComplementaryEssentialCircleArcsNonhomotopic S c d b1 hd hb1 hinter hcover hterminal
  have hActualCurveEmbeddedArcComplement (S : Type) [TopologicalSpace S] [T2Space S]
      (c : Curve S) (k : C(Interval,S)) (hk : Topology.IsEmbedding k)
      (hkc : Set.range k ⊆ c.image) :
      ∃ d : C(Interval,S),Topology.IsEmbedding d ∧ d 0=k 0 ∧ d 1=k 1 ∧
        Set.range k ∪ Set.range d=c.image ∧
        Set.range k ∩ Set.range d={k 0,k 1} := by
    let τ : Interval := ⟨1/2,by norm_num⟩
    have hτ : τ∈Set.Ioo (0 : Interval) 1 := by
      constructor
      · change (0:ℝ)<1/2;norm_num
      · change (1/2:ℝ)<1;norm_num
    have hx : k 0≠k 1 := by
      intro he
      have hv := congrArg (fun t : Interval => (t:ℝ)) (hk.injective he)
      norm_num at hv
    obtain ⟨p,q,hp,hq,hp0,hq0,hp1,hq1,hcover,hinter⟩ := source_curve_complementary_arcs c
      (k 0) (k 1) (hkc (Set.mem_range_self 0)) (hkc (Set.mem_range_self 1)) hx
    have hIpre : IsPreconnected (Set.Ioo (0 : Interval) 1) := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      have he : Subtype.val '' Set.Ioo (0 : Interval) 1=Set.Ioo (0:ℝ) 1 := by
        ext t
        constructor
        · rintro ⟨u,hu,rfl⟩
          exact hu
        · intro ht
          exact ⟨⟨t,⟨ht.1.le,ht.2.le⟩⟩,ht,rfl⟩
      rw [he]
      exact isPreconnected_Ioo
    let K := k '' Set.Ioo (0 : Interval) 1
    have hKpre : IsPreconnected K := hIpre.image k k.continuous.continuousOn
    have hKend (y : S) (hy : y∈K) : y∉({k 0,k 1} : Set S) := by
      obtain ⟨t,ht,rfl⟩ := hy
      intro hn
      rcases Set.mem_insert_iff.mp hn with h0 | h1
      · exact (ne_of_gt ht.1) (hk.injective h0)
      · exact (ne_of_lt ht.2) (hk.injective (Set.mem_singleton_iff.mp h1))
    have hsub (p q : C(Interval,S)) (hp : Topology.IsEmbedding p) (hq : Topology.IsEmbedding q)
        (hp0 : p 0=k 0) (hp1 : p 1=k 1)
        (hcover : Set.range p ∪ Set.range q=c.image)
        (hinter : Set.range p ∩ Set.range q={k 0,k 1})
        (hm : k τ∈Set.range p) : Set.range k=Set.range p := by
      have hmK : k τ∈K := ⟨τ,hτ,rfl⟩
      have hmN : k τ∉Set.range q := fun hn => hKend _ hmK (hinter ▸ ⟨hm,hn⟩)
      have hpc : IsClosed (Set.range p) := (isCompact_range p.continuous).isClosed
      have hqc : IsClosed (Set.range q) := (isCompact_range q.continuous).isClosed
      have hKcover : K⊆(Set.range q)ᶜ ∪ (Set.range p)ᶜ := by
        intro y hy
        by_cases hn : y∈Set.range q
        · right
          intro hp
          exact hKend y hy (hinter ▸ ⟨hp,hn⟩)
        · exact Or.inl hn
      have hKP : K⊆Set.range p := by
        intro y hy
        by_contra hn
        obtain ⟨z,hz⟩ := hKpre (Set.range q)ᶜ (Set.range p)ᶜ
          hqc.isOpen_compl hpc.isOpen_compl hKcover ⟨k τ,hmK,hmN⟩ ⟨y,hy,hn⟩
        have hzc : z∈c.image := hkc (Set.image_subset_range _ _ hz.1)
        have hzp : z∈Set.range p ∪ Set.range q := hcover.symm ▸ hzc
        exact hzp.elim hz.2.2 hz.2.1
      have hwhole : Set.range k⊆Set.range p := by
        rintro y ⟨t,rfl⟩
        by_cases ht0 : t=0
        · exact ⟨0,hp0.trans (congrArg k ht0).symm⟩
        by_cases ht1 : t=1
        · exact ⟨1,hp1.trans (congrArg k ht1).symm⟩
        exact hKP ⟨t,⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
          lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩
      let P : Path (k 0) (k 1) := ⟨p,hp0,hp1⟩
      let A : Path (k 0) (k 1) := ⟨k,rfl,rfl⟩
      exact LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.range_eq_of_subset_of_injective P A hp.injective hwhole
    have hm : k τ∈Set.range p ∪ Set.range q := hcover.symm ▸ hkc (Set.mem_range_self τ)
    rcases hm with hm | hm
    · have he := hsub p q hp hq hp0 hp1 hcover hinter hm
      exact ⟨q,hq,hq0,hq1,he.symm ▸ hcover,he.symm ▸ hinter⟩
    · have hc' : Set.range q ∪ Set.range p=c.image := by rw [Set.union_comm];exact hcover
      have hi' : Set.range q ∩ Set.range p={k 0,k 1} := by rw [Set.inter_comm];exact hinter
      have he := hsub q p hq hp hq0 hq1 hc' hi' hm
      exact ⟨p,hp,hp0,hp1,he.symm ▸ hc',he.symm ▸ hi'⟩
  have hActualFullBandCircleProperArcWithComplement (F B : Set S) (c : Curve S)
      (hc : c.image ⊆ interior F)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F)) (hE : Topology.IsEmbedding E)
      (hbase : ∀ w,(E (0,w)).val∈B)
      (hinside : ∀ t : Interval,0<(t:ℝ) → ∀ w,(E (t,w)).val∈interior F)
      (hcircle : ∀ z,(E z).val∈c.image ↔ z.1=1) :
      ∃ A : C(Interval,↥F),Topology.IsEmbedding A ∧
        (A 0).val∈B ∧ (A 1).val∈B ∧
        (∀ t∈Set.Ioo (0 : Interval) 1,(A t).val∈interior F) := by
    let P : C(Interval,S) := ⟨fun t => (E (t,⟨1,by norm_num⟩)).val,
      continuous_subtype_val.comp (E.continuous.comp (continuous_id.prodMk continuous_const))⟩
    let Q : C(Interval,S) := ⟨fun t => (E (t,⟨-1,by norm_num⟩)).val,
      continuous_subtype_val.comp (E.continuous.comp (continuous_id.prodMk continuous_const))⟩
    have hiP : Function.Injective P := by
      intro t s hts
      have he := hE.injective (Subtype.ext hts)
      exact congrArg Prod.fst he
    have hiQ : Function.Injective Q := by
      intro t s hts
      have he := hE.injective (Subtype.ext hts)
      exact congrArg Prod.fst he
    have hPQ : Disjoint (Set.range P) (Set.range Q) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨s,rfl⟩ ⟨t,he⟩
      have hv := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2:ℝ))
        (hE.injective (Subtype.ext he))
      norm_num at hv
    let k : C(Interval,S) := ⟨fun t => (E (1,⟨1-2*(t:ℝ),by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩)).val,by fun_prop⟩
    have hki : Function.Injective k := by
      intro t u htu
      have he := hE.injective (Subtype.ext htu)
      have hv := congrArg (fun z : Interval × Set.Icc (-1:ℝ) 1 => (z.2:ℝ)) he
      dsimp at hv
      apply Subtype.ext
      linarith
    have hk : Topology.IsEmbedding k := (k.continuous.isClosedEmbedding hki).isEmbedding
    have hkc : Set.range k⊆c.image := by
      rintro y ⟨t,rfl⟩
      exact (hcircle _).mpr rfl
    have hk0 : k 0=P 1 := by dsimp [k,P];norm_num
    have hk1 : k 1=Q 1 := by dsimp [k,Q];norm_num
    obtain ⟨d,hd,hd0',hd1',hdcover,hdinter⟩ := hActualCurveEmbeddedArcComplement S c k hk hkc
    have hd0 : d 0=P 1 := hd0'.trans hk0
    have hd1 : d 1=Q 1 := hd1'.trans hk1
    have hdc : Set.range d⊆c.image := fun y hy => hdcover ▸ Or.inr hy
    have hPC (t : Interval) : P t∈c.image ↔ t=1 := hcircle _
    have hQC (t : Interval) : Q t∈c.image ↔ t=1 := hcircle _
    let p : Path (P 0) (P 1) := ⟨P,rfl,rfl⟩
    let q : Path (P 1) (Q 1) := ⟨d,hd0,hd1⟩
    let m : Path (Q 0) (Q 1) := ⟨Q,rfl,rfl⟩
    have hpq : Set.range p ∩ Set.range q={P 1} := by
      ext y
      constructor
      · rintro ⟨⟨t,ht⟩,hyq⟩
        have ht1 : t=1 := (hPC t).mp (ht.symm ▸ hdc hyq)
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg p ht1).trans p.target))
      · rintro rfl
        exact ⟨⟨1,rfl⟩,⟨0,hd0⟩⟩
    have hqm : Set.range q ∩ Set.range m.symm={Q 1} := by
      rw [Path.symm_range]
      ext y
      constructor
      · rintro ⟨hyq,⟨t,ht⟩⟩
        have ht1 : t=1 := (hQC t).mp (ht.symm ▸ hdc hyq)
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg m ht1).trans m.target))
      · rintro rfl
        exact ⟨⟨1,hd1⟩,⟨1,rfl⟩⟩
    have hjoin : Set.range (p.trans q) ∩ Set.range m.symm={Q 1} := by
      rw [Path.trans_range,Set.union_inter_distrib_right,hqm,Path.symm_range]
      have he : Set.range p ∩ Set.range m=∅ := Set.disjoint_iff_inter_eq_empty.mp hPQ
      rw [he,Set.empty_union]
    have hpqi := hSimpleConcat p q hiP hd.injective hpq
    have hi := hSimpleConcat (p.trans q) m.symm hpqi
      (hiQ.comp unitInterval.symm_involutive.injective) hjoin
    let r : C(Interval,S) := ⟨(p.trans q).trans m.symm,((p.trans q).trans m.symm).continuous⟩
    have hr0 : r 0=P 0 := ((p.trans q).trans m.symm).source
    have hr1 : r 1=Q 0 := ((p.trans q).trans m.symm).target
    have hrange : Set.range r=(Set.range P ∪ Set.range d) ∪ Set.range Q := by
      change Set.range ((p.trans q).trans m.symm)=_
      rw [Path.trans_range,Path.trans_range,Path.symm_range]
      rfl
    have hrF (t : Interval) : r t∈F := by
      have ht := Set.mem_range_self (f := r) t
      rw [hrange] at ht
      rcases ht with (hP | hd) | hQ
      · obtain ⟨u,hu⟩ := hP
        exact hu ▸ (E (u,⟨1,by norm_num⟩)).property
      · exact interior_subset (hc (hdc hd))
      · obtain ⟨u,hu⟩ := hQ
        exact hu ▸ (E (u,⟨-1,by norm_num⟩)).property
    let A : C(Interval,↥F) := ⟨fun t => ⟨r t,hrF t⟩,r.continuous.subtype_mk _⟩
    have hAi : Function.Injective A := by
      intro t u he
      exact hi (congrArg Subtype.val he)
    refine ⟨A,(A.continuous.isClosedEmbedding hAi).isEmbedding,?_,?_,?_⟩
    · change r 0∈B
      rw [hr0]
      exact hbase _
    · change r 1∈B
      rw [hr1]
      exact hbase _
    · intro t ht
      change r t∈interior F
      have hrt := Set.mem_range_self (f := r) t
      rw [hrange] at hrt
      rcases hrt with (hP | hd) | hQ
      · obtain ⟨u,hu⟩ := hP
        have hu0 : u≠0 := by
          intro he
          have hrt0 : r t=r 0 := hu.symm.trans ((congrArg P he).trans hr0.symm)
          exact (ne_of_gt ht.1) (hi hrt0)
        exact hu ▸ hinside u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm))) _
      · exact hc (hdc hd)
      · obtain ⟨u,hu⟩ := hQ
        have hu0 : u≠0 := by
          intro he
          have hrt1 : r t=r 1 := hu.symm.trans ((congrArg Q he).trans hr1.symm)
          exact (ne_of_lt ht.2) (hi hrt1)
        exact hu ▸ hinside u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm))) _
  have hActualFullBandOrientedDiskExclusion (F B : Set S) (c : EssentialCurve S)
      (hc : c.val.image ⊆ interior F)
      (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
      (center : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hR : 0<R)
      (htarget : Metric.closedBall center R⊆e.target)
      (hBD : B⊆e.symm '' Metric.closedBall center R)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F)) (hE : Topology.IsEmbedding E)
      (hbase : ∀ w,(E (0,w)).val∈B)
      (hinside : ∀ t : Interval,0<(t:ℝ) → ∀ w,(E (t,w)).val∈interior F)
      (hcircle : ∀ z,(E z).val∈c.val.image ↔ z.1=1) :
      ∃ A : C(Interval,↥F),Topology.IsEmbedding A ∧
        (A 0).val∈B ∧ (A 1).val∈B ∧
        (∀ t∈Set.Ioo (0 : Interval) 1,(A t).val∈interior F) ∧
        ∀ b : C(Interval,↥F),(∀ t,(b t).val∈B) →
          ((b 0=A 0 ∧ b 1=A 1) ∨ (b 0=A 1 ∧ b 1=A 0)) →
          ¬ ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
            Topology.IsEmbedding D ∧
            D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
              Set.range A ∪ Set.range b := by
    let P : C(Interval,S) := ⟨fun t => (E (t,⟨1,by norm_num⟩)).val,
      continuous_subtype_val.comp (E.continuous.comp (continuous_id.prodMk continuous_const))⟩
    let Q : C(Interval,S) := ⟨fun t => (E (t,⟨-1,by norm_num⟩)).val,
      continuous_subtype_val.comp (E.continuous.comp (continuous_id.prodMk continuous_const))⟩
    have hiP : Function.Injective P := by
      intro t s hts
      have he := hE.injective (Subtype.ext hts)
      exact congrArg Prod.fst he
    have hiQ : Function.Injective Q := by
      intro t s hts
      have he := hE.injective (Subtype.ext hts)
      exact congrArg Prod.fst he
    have hPQ : Disjoint (Set.range P) (Set.range Q) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨s,rfl⟩ ⟨t,he⟩
      have hv := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2:ℝ))
        (hE.injective (Subtype.ext he))
      norm_num at hv
    let k : C(Interval,S) := ⟨fun t => (E (1,⟨1-2*(t:ℝ),by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩)).val,by fun_prop⟩
    have hki : Function.Injective k := by
      intro t u htu
      have he := hE.injective (Subtype.ext htu)
      have hv := congrArg (fun z : Interval × Set.Icc (-1:ℝ) 1 => (z.2:ℝ)) he
      dsimp at hv
      apply Subtype.ext
      linarith
    have hk : Topology.IsEmbedding k := (k.continuous.isClosedEmbedding hki).isEmbedding
    have hkc : Set.range k⊆c.val.image := by
      rintro y ⟨t,rfl⟩
      exact (hcircle _).mpr rfl
    have hk0 : k 0=P 1 := by dsimp [k,P];norm_num
    have hk1 : k 1=Q 1 := by dsimp [k,Q];norm_num
    obtain ⟨d,hd,hd0',hd1',hdcover,hdinter⟩ := hActualCurveEmbeddedArcComplement S c.val k hk hkc
    have hd0 : d 0=P 1 := hd0'.trans hk0
    have hd1 : d 1=Q 1 := hd1'.trans hk1
    have hdc : Set.range d⊆c.val.image := fun y hy => hdcover ▸ Or.inr hy
    have hPC (t : Interval) : P t∈c.val.image ↔ t=1 := hcircle _
    have hQC (t : Interval) : Q t∈c.val.image ↔ t=1 := hcircle _
    let p : Path (P 0) (P 1) := ⟨P,rfl,rfl⟩
    let q : Path (P 1) (Q 1) := ⟨d,hd0,hd1⟩
    let m : Path (Q 0) (Q 1) := ⟨Q,rfl,rfl⟩
    have hpq : Set.range p ∩ Set.range q={P 1} := by
      ext y
      constructor
      · rintro ⟨⟨t,ht⟩,hyq⟩
        have ht1 : t=1 := (hPC t).mp (ht.symm ▸ hdc hyq)
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg p ht1).trans p.target))
      · rintro rfl
        exact ⟨⟨1,rfl⟩,⟨0,hd0⟩⟩
    have hqm : Set.range q ∩ Set.range m.symm={Q 1} := by
      rw [Path.symm_range]
      ext y
      constructor
      · rintro ⟨hyq,⟨t,ht⟩⟩
        have ht1 : t=1 := (hQC t).mp (ht.symm ▸ hdc hyq)
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg m ht1).trans m.target))
      · rintro rfl
        exact ⟨⟨1,hd1⟩,⟨1,rfl⟩⟩
    have hjoin : Set.range (p.trans q) ∩ Set.range m.symm={Q 1} := by
      rw [Path.trans_range,Set.union_inter_distrib_right,hqm,Path.symm_range]
      have he : Set.range p ∩ Set.range m=∅ := Set.disjoint_iff_inter_eq_empty.mp hPQ
      rw [he,Set.empty_union]
    have hpqi := hSimpleConcat p q hiP hd.injective hpq
    have hi := hSimpleConcat (p.trans q) m.symm hpqi
      (hiQ.comp unitInterval.symm_involutive.injective) hjoin
    let r : C(Interval,S) := ⟨(p.trans q).trans m.symm,((p.trans q).trans m.symm).continuous⟩
    have hr0 : r 0=P 0 := ((p.trans q).trans m.symm).source
    have hr1 : r 1=Q 0 := ((p.trans q).trans m.symm).target
    have hrange : Set.range r=(Set.range P ∪ Set.range d) ∪ Set.range Q := by
      change Set.range ((p.trans q).trans m.symm)=_
      rw [Path.trans_range,Path.trans_range,Path.symm_range]
      rfl
    have hrF (t : Interval) : r t∈F := by
      have ht := Set.mem_range_self (f := r) t
      rw [hrange] at ht
      rcases ht with (hP | hd) | hQ
      · obtain ⟨u,hu⟩ := hP
        exact hu ▸ (E (u,⟨1,by norm_num⟩)).property
      · exact interior_subset (hc (hdc hd))
      · obtain ⟨u,hu⟩ := hQ
        exact hu ▸ (E (u,⟨-1,by norm_num⟩)).property
    let A : C(Interval,↥F) := ⟨fun t => ⟨r t,hrF t⟩,r.continuous.subtype_mk _⟩
    have hAi : Function.Injective A := by
      intro t u he
      exact hi (congrArg Subtype.val he)
    refine ⟨A,(A.continuous.isClosedEmbedding hAi).isEmbedding,?_,?_,?_,?_⟩
    · change r 0∈B
      rw [hr0]
      exact hbase _
    · change r 1∈B
      rw [hr1]
      exact hbase _
    · intro t ht
      change r t∈interior F
      have hrt := Set.mem_range_self (f := r) t
      rw [hrange] at hrt
      rcases hrt with (hP | hd) | hQ
      · obtain ⟨u,hu⟩ := hP
        have hu0 : u≠0 := by
          intro he
          have hrt0 : r t=r 0 := hu.symm.trans ((congrArg P he).trans hr0.symm)
          exact (ne_of_gt ht.1) (hi hrt0)
        exact hu ▸ hinside u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm))) _
      · exact hc (hdc hd)
      · obtain ⟨u,hu⟩ := hQ
        have hu0 : u≠0 := by
          intro he
          have hrt1 : r t=r 1 := hu.symm.trans ((congrArg Q he).trans hr1.symm)
          exact (ne_of_lt ht.2) (hi hrt1)
        exact hu ▸ hinside u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm))) _
    · intro b hb hend
      rintro ⟨D,hD,hDb⟩
      let bS : C(Interval,S) := ⟨fun t => (b t).val,continuous_subtype_val.comp b.continuous⟩
      obtain ⟨β,hβrange⟩ : ∃ β : Path (P 0) (Q 0),Set.range β=Set.range bS := by
        rcases hend with ⟨hb0,hb1⟩ | ⟨hb0,hb1⟩
        · have hs : bS 0=P 0 := (congrArg (fun u : ↥F => (u:S)) hb0).trans hr0
          have ht : bS 1=Q 0 := (congrArg (fun u : ↥F => (u:S)) hb1).trans hr1
          exact ⟨⟨bS,hs,ht⟩,rfl⟩
        · have hs : bS 1=P 0 := (congrArg (fun u : ↥F => (u:S)) hb1).trans hr0
          have ht : bS 0=Q 0 := (congrArg (fun u : ↥F => (u:S)) hb0).trans hr1
          let bP : Path (bS 0) (bS 1) := ⟨bS,rfl,rfl⟩
          refine ⟨bP.symm.cast hs.symm ht.symm,?_⟩
          change Set.range bP.symm=Set.range bS
          rw [Path.symm_range]
          rfl
      let DS : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
        ⟨fun z => (D z).val,continuous_subtype_val.comp D.continuous⟩
      have hDS : Topology.IsEmbedding DS := Topology.IsEmbedding.subtypeVal.comp hD
      have hDSboundary : DS '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
          Set.range r ∪ Set.range bS := by
        change (Subtype.val ∘ D) '' _ = _
        rw [Set.image_comp,hDb,Set.image_union,←Set.range_comp,←Set.range_comp]
        rfl
      let ES : C(Interval × Set.Icc (-1:ℝ) 1,S) :=
        ⟨fun z => (E z).val,continuous_subtype_val.comp E.continuous⟩
      obtain ⟨p',m',b0,b1,hp',hm',hb0,hb1,hband⟩ := hActualFullBandBoundaryPathRelation ES
      have hep : p'=p := Path.ext (funext hp')
      have hem : m'=m := Path.ext (funext hm')
      rw [hep,hem] at hband
      have hb1k : Set.range b1=Set.range k := by
        have he : (b1 : Interval → S)=k := funext hb1
        exact congrArg Set.range he
      have hb1i : Function.Injective b1 := by
        intro t u he
        apply hki
        exact (hb1 t).symm.trans (he.trans (hb1 u))
      have hb1e : Topology.IsEmbedding b1 := (b1.continuous.isClosedEmbedding hb1i).isEmbedding
      have hcirclecover : Set.range q ∪ Set.range b1=c.val.image := by
        rw [hb1k,Set.union_comm]
        exact hdcover
      have hcircleinter : Set.range q ∩ Set.range b1={P 1,Q 1} := by
        change Set.range d ∩ Set.range b1={P 1,Q 1}
        rw [hb1k,Set.inter_comm,hdinter,hk0,hk1]
      have hβD : Set.range β⊆e.symm '' Metric.closedBall center R := by
        intro y hy
        rw [hβrange] at hy
        obtain ⟨t,rfl⟩ := hy
        exact hBD (hb t)
      have hb0D : Set.range b0⊆e.symm '' Metric.closedBall center R := by
        rintro y ⟨t,rfl⟩
        rw [hb0]
        exact hBD (hbase _)
      have hβb0 : β.Homotopic b0 := hActualChartClosedDiskPathsHomotopic e center R hR htarget β b0 hβD hb0D
      have hArcDisk : ((p.trans q).trans m.symm).Homotopic β := by
        apply hActualEmbeddedDiskPathsHomotopic DS hDS
        · intro y hy
          have hh : y∈DS '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
            hDSboundary.symm ▸ Or.inl hy
          exact Set.image_subset_range _ _ hh
        · intro y hy
          have hh : y∈DS '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
            hDSboundary.symm ▸ Or.inr (hβrange ▸ hy)
          exact Set.image_subset_range _ _ hh
      exact hActualBandDiskEssentialCircleContradiction S c p m b0 b1 q hb1e hd
        hcircleinter hcirclecover hband (hArcDisk.trans hβb0)
  have hActualFullBandUnorientedDiskExclusion (F B : Set S)
      (hBF : B⊆frontier F) (c : EssentialCurve S)
      (hc : c.val.image⊆interior F)
      (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
      (center : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hR : 0<R)
      (htarget : Metric.closedBall center R⊆e.target)
      (hBD : B⊆e.symm '' Metric.closedBall center R)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F)) (hE : Topology.IsEmbedding E)
      (hbase : ∀ w,(E (0,w)).val∈B)
      (hinside : ∀ t : Interval,0<(t:ℝ) → ∀ w,(E (t,w)).val∈interior F)
      (hcircle : ∀ z,(E z).val∈c.val.image ↔ z.1=1) :
      ∃ A : C(Interval,↥F),Topology.IsEmbedding A ∧
        (A 0).val∈B ∧ (A 1).val∈B ∧
        (∀ t∈Set.Ioo (0 : Interval) 1,(A t).val∉frontier F) ∧
        ¬ (∃ b : C(Interval,↥F),Topology.IsEmbedding b ∧
          (∀ t,(b t).val∈B) ∧
          ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
            Topology.IsEmbedding D ∧
            D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
              Set.range A ∪ Set.range b) := by
    obtain ⟨A,hA,hA0,hA1,hAI,hno⟩ :=
      hActualFullBandOrientedDiskExclusion F B c hc e center R hR htarget hBD E hE hbase hinside hcircle
    have hAF (t : Interval) (ht : t∈Set.Ioo (0 : Interval) 1) : (A t).val∉frontier F := by
      exact fun hf => Set.disjoint_left.mp disjoint_interior_frontier (hAI t ht) hf
    refine ⟨A,hA,hA0,hA1,hAF,?_⟩
    rintro ⟨b,hb,hbB,D,hD,hboundary⟩
    have hAB (t : Interval) (ht : t∈Set.Ioo (0 : Interval) 1) :
        A t∉{y : ↥F | y.val∈B} := fun hB => hAF t ht (hBF hB)
    have hbrange : Set.range b⊆{y : ↥F | y.val∈B} := by
      rintro y ⟨t,rfl⟩
      exact hbB t
    have hend := actual_disk_boundary_two_arcs_forces_endpoint_orientation
      {y : ↥F | y.val∈B} A b hA hb hA0 hA1 hAB hbrange D hD hboundary
    exact hno b hbB hend ⟨D,hD,hboundary⟩
  have hActualLooseAmbientCapsOrientedDiskExclusion
      (F B : Set S) (c : EssentialCurve S) (hc : c.val.image⊆interior F)
      (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
      (center : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (hR : 0<R)
      (htarget : Metric.closedBall center R⊆e.target)
      (hBD : B⊆e.symm '' Metric.closedBall center R)
      (e₁ : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
      (center₁ : EuclideanSpace ℝ (Fin 2)) (R₁ : ℝ) (hR₁ : 0<R₁)
      (htarget₁ : Metric.closedBall center₁ R₁⊆e₁.target)
      (P₀ Q₀ : C(Interval,↥F)) (hP₀ : Topology.IsEmbedding P₀) (hQ₀ : Topology.IsEmbedding Q₀)
      (hbaseP : (P₀ 0).val∈B) (hbaseQ : (Q₀ 0).val∈B)
      (hinsideP : ∀ t : Interval,0<(t:ℝ) → (P₀ t).val∈interior F)
      (hinsideQ : ∀ t : Interval,0<(t:ℝ) → (Q₀ t).val∈interior F)
      (hcircleP : ∀ t,(P₀ t).val∈c.val.image ↔ t=1)
      (hcircleQ : ∀ t,(Q₀ t).val∈c.val.image ↔ t=1)
      (hdisjointPQ : Disjoint (Set.range (fun t => (P₀ t).val)) (Set.range (fun t => (Q₀ t).val)))
      (M : C(Interval × Set.Icc (-1 : ℝ) 1,S))
      (hMP : ∀ t,M (t,⟨1,by norm_num⟩)=(P₀ t).val)
      (hMQ : ∀ t,M (t,⟨-1,by norm_num⟩)=(Q₀ t).val)
      (hM₀ : ∀ w,M (0,w)∈e.symm '' Metric.closedBall center R)
      (hM₁ : ∀ w,M (1,w)∈e₁.symm '' Metric.closedBall center₁ R₁)
      (k : C(Interval,S)) (hk : Topology.IsEmbedding k)
      (hkc : Set.range k⊆c.val.image)
      (hk0 : k 0=(P₀ 1).val) (hk1 : k 1=(Q₀ 1).val)
      (hkD : Set.range k⊆e₁.symm '' Metric.closedBall center₁ R₁) :
      ∃ A : C(Interval,↥F),Topology.IsEmbedding A ∧
        (A 0).val∈B ∧ (A 1).val∈B ∧
        (∀ t∈Set.Ioo (0 : Interval) 1,(A t).val∈interior F) ∧
        ∀ b : C(Interval,↥F),(∀ t,(b t).val∈B) →
          ((b 0=A 0 ∧ b 1=A 1) ∨ (b 0=A 1 ∧ b 1=A 0)) →
          ¬ ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
            Topology.IsEmbedding D ∧
            D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
              Set.range A ∪ Set.range b := by
    let P : C(Interval,S) := ⟨fun t => (P₀ t).val,continuous_subtype_val.comp P₀.continuous⟩
    let Q : C(Interval,S) := ⟨fun t => (Q₀ t).val,continuous_subtype_val.comp Q₀.continuous⟩
    have hiP : Function.Injective P := fun t u he => hP₀.injective (Subtype.ext he)
    have hiQ : Function.Injective Q := fun t u he => hQ₀.injective (Subtype.ext he)
    have hPQ : Disjoint (Set.range P) (Set.range Q) := hdisjointPQ
    obtain ⟨d,hd,hd0',hd1',hdcover,hdinter⟩ := hActualCurveEmbeddedArcComplement S c.val k hk hkc
    have hd0 : d 0=P 1 := hd0'.trans hk0
    have hd1 : d 1=Q 1 := hd1'.trans hk1
    have hdc : Set.range d⊆c.val.image := fun y hy => hdcover ▸ Or.inr hy
    have hPC (t : Interval) : P t∈c.val.image ↔ t=1 := hcircleP t
    have hQC (t : Interval) : Q t∈c.val.image ↔ t=1 := hcircleQ t
    let p : Path (P 0) (P 1) := ⟨P,rfl,rfl⟩
    let q : Path (P 1) (Q 1) := ⟨d,hd0,hd1⟩
    let m : Path (Q 0) (Q 1) := ⟨Q,rfl,rfl⟩
    have hpq : Set.range p ∩ Set.range q={P 1} := by
      ext y
      constructor
      · rintro ⟨⟨t,ht⟩,hyq⟩
        have ht1 : t=1 := (hPC t).mp (ht.symm ▸ hdc hyq)
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg p ht1).trans p.target))
      · rintro rfl
        exact ⟨⟨1,rfl⟩,⟨0,hd0⟩⟩
    have hqm : Set.range q ∩ Set.range m.symm={Q 1} := by
      rw [Path.symm_range]
      ext y
      constructor
      · rintro ⟨hyq,⟨t,ht⟩⟩
        have ht1 : t=1 := (hQC t).mp (ht.symm ▸ hdc hyq)
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg m ht1).trans m.target))
      · rintro rfl
        exact ⟨⟨1,hd1⟩,⟨1,rfl⟩⟩
    have hjoin : Set.range (p.trans q) ∩ Set.range m.symm={Q 1} := by
      rw [Path.trans_range,Set.union_inter_distrib_right,hqm,Path.symm_range]
      have he : Set.range p ∩ Set.range m=∅ := Set.disjoint_iff_inter_eq_empty.mp hPQ
      rw [he,Set.empty_union]
    have hpqi := hSimpleConcat p q hiP hd.injective hpq
    have hi := hSimpleConcat (p.trans q) m.symm hpqi
      (hiQ.comp unitInterval.symm_involutive.injective) hjoin
    let r : C(Interval,S) := ⟨(p.trans q).trans m.symm,((p.trans q).trans m.symm).continuous⟩
    have hr0 : r 0=P 0 := ((p.trans q).trans m.symm).source
    have hr1 : r 1=Q 0 := ((p.trans q).trans m.symm).target
    have hrange : Set.range r=(Set.range P ∪ Set.range d) ∪ Set.range Q := by
      change Set.range ((p.trans q).trans m.symm)=_
      rw [Path.trans_range,Path.trans_range,Path.symm_range]
      rfl
    have hrF (t : Interval) : r t∈F := by
      have ht := Set.mem_range_self (f := r) t
      rw [hrange] at ht
      rcases ht with (hP | hd) | hQ
      · obtain ⟨u,hu⟩ := hP
        exact hu ▸ (P₀ u).property
      · exact interior_subset (hc (hdc hd))
      · obtain ⟨u,hu⟩ := hQ
        exact hu ▸ (Q₀ u).property
    let A : C(Interval,↥F) := ⟨fun t => ⟨r t,hrF t⟩,r.continuous.subtype_mk _⟩
    have hAi : Function.Injective A := by
      intro t u he
      exact hi (congrArg Subtype.val he)
    refine ⟨A,(A.continuous.isClosedEmbedding hAi).isEmbedding,?_,?_,?_,?_⟩
    · change r 0∈B
      rw [hr0]
      exact hbaseP
    · change r 1∈B
      rw [hr1]
      exact hbaseQ
    · intro t ht
      change r t∈interior F
      have hrt := Set.mem_range_self (f := r) t
      rw [hrange] at hrt
      rcases hrt with (hP | hd) | hQ
      · obtain ⟨u,hu⟩ := hP
        have hu0 : u≠0 := by
          intro he
          have hrt0 : r t=r 0 := hu.symm.trans ((congrArg P he).trans hr0.symm)
          exact (ne_of_gt ht.1) (hi hrt0)
        exact hu ▸ hinsideP u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm)))
      · exact hc (hdc hd)
      · obtain ⟨u,hu⟩ := hQ
        have hu0 : u≠0 := by
          intro he
          have hrt1 : r t=r 1 := hu.symm.trans ((congrArg Q he).trans hr1.symm)
          exact (ne_of_lt ht.2) (hi hrt1)
        exact hu ▸ hinsideQ u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm)))
    · intro b hb hend
      rintro ⟨D,hD,hDb⟩
      let bS : C(Interval,S) := ⟨fun t => (b t).val,continuous_subtype_val.comp b.continuous⟩
      obtain ⟨β,hβrange⟩ : ∃ β : Path (P 0) (Q 0),Set.range β=Set.range bS := by
        rcases hend with ⟨hb0,hb1⟩ | ⟨hb0,hb1⟩
        · have hs : bS 0=P 0 := (congrArg (fun u : ↥F => (u:S)) hb0).trans hr0
          have ht : bS 1=Q 0 := (congrArg (fun u : ↥F => (u:S)) hb1).trans hr1
          exact ⟨⟨bS,hs,ht⟩,rfl⟩
        · have hs : bS 1=P 0 := (congrArg (fun u : ↥F => (u:S)) hb1).trans hr0
          have ht : bS 0=Q 0 := (congrArg (fun u : ↥F => (u:S)) hb0).trans hr1
          let bP : Path (bS 0) (bS 1) := ⟨bS,rfl,rfl⟩
          refine ⟨bP.symm.cast hs.symm ht.symm,?_⟩
          change Set.range bP.symm=Set.range bS
          rw [Path.symm_range]
          rfl
      let DS : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
        ⟨fun z => (D z).val,continuous_subtype_val.comp D.continuous⟩
      have hDS : Topology.IsEmbedding DS := Topology.IsEmbedding.subtypeVal.comp hD
      have hDSboundary : DS '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
          Set.range r ∪ Set.range bS := by
        change (Subtype.val ∘ D) '' _ = _
        rw [Set.image_comp,hDb,Set.image_union,←Set.range_comp,←Set.range_comp]
        rfl
      obtain ⟨b0,b1,hb0,hb1,hband⟩ :=
        actual_ambient_rectangle_boundary_relation_with_named_rails M p m hMP hMQ
      let kP : Path (P 1) (Q 1) := ⟨k,hk0,hk1⟩
      have hb1D : Set.range b1⊆e₁.symm '' Metric.closedBall center₁ R₁ := by
        rintro y ⟨t,rfl⟩
        rw [hb1]
        exact hM₁ _
      have hb1k : b1.Homotopic kP :=
        hActualChartClosedDiskPathsHomotopic e₁ center₁ R₁ hR₁ htarget₁ b1 kP hb1D hkD
      have hbandK : (p.trans kP).Homotopic (b0.trans m) :=
        ((Path.Homotopic.refl p).hcomp hb1k.symm).trans hband
      have hcirclecover : Set.range q ∪ Set.range kP=c.val.image := by
        change Set.range d ∪ Set.range k=c.val.image
        rw [Set.union_comm]
        exact hdcover
      have hcircleinter : Set.range q ∩ Set.range kP={P 1,Q 1} := by
        change Set.range d ∩ Set.range k={P 1,Q 1}
        rw [Set.inter_comm,hdinter,hk0,hk1]
        rfl
      have hβD : Set.range β⊆e.symm '' Metric.closedBall center R := by
        intro y hy
        rw [hβrange] at hy
        obtain ⟨t,rfl⟩ := hy
        exact hBD (hb t)
      have hb0D : Set.range b0⊆e.symm '' Metric.closedBall center R := by
        rintro y ⟨t,rfl⟩
        rw [hb0]
        exact hM₀ _
      have hβb0 : β.Homotopic b0 := hActualChartClosedDiskPathsHomotopic e center R hR htarget β b0 hβD hb0D
      have hArcDisk : ((p.trans q).trans m.symm).Homotopic β := by
        apply hActualEmbeddedDiskPathsHomotopic DS hDS
        · intro y hy
          have hh : y∈DS '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
            hDSboundary.symm ▸ Or.inl hy
          exact Set.image_subset_range _ _ hh
        · intro y hy
          have hh : y∈DS '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
            hDSboundary.symm ▸ Or.inr (hβrange ▸ hy)
          exact Set.image_subset_range _ _ hh
      exact hActualBandDiskEssentialCircleContradiction S c p m b0 kP q hk hd
        hcircleinter hcirclecover hbandK (hArcDisk.trans hβb0)
  let j : J := Classical.choice inferInstance
  obtain ⟨c₀,a,ha,hc₀,_,haB,hac,haf,_,hai⟩ :=
    hActualGenericEssentialCircleEmbeddedCleanAccess j
  have haContact : ∀ t,(a t).val∈boundaryCircle ↔ t=0 := by
    intro t
    constructor
    · intro ht
      exact (haf t).mp (hActualBaseInFrontier ht)
    · rintro rfl
      exact haB
  obtain ⟨N₀,η₀,hp₀,hz₀,hη₀,_,ht₀,hl₀⟩ :=
    hActualGenericSuppliedConnectorHalfPlane a ha haContact hai
  obtain ⟨N₁,η₁,hp₁,hz₁,hη₁,_,ht₁,hl₁⟩ :=
    hActualSuppliedConnectorTerminalRayLine F c₀.val hc₀ a ha hac
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let center := e x
  obtain ⟨R',hRR',hR'target⟩ :=
    actual_original_chart_closed_disk_ambient_cap_radius_enlargement e center R hR htarget
  have hR' : 0<R' := hR.trans hRR'
  let U₀ : Set S := e.symm '' Metric.ball center R'
  have hU₀ : IsOpen U₀ := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans hR'target)
  have hBU₀ : boundaryCircle⊆U₀ :=
    Set.image_mono (Metric.sphere_subset_ball hRR')
  have hBD : boundaryCircle⊆e.symm '' Metric.closedBall center R' :=
    hBU₀.trans (Set.image_mono Metric.ball_subset_closedBall)
  have hzeroN : (0 : Schoenflies.Plane)∈N₁.target := hz₁ ▸ N₁.map_source hp₁
  obtain ⟨ε,hε,hεtarget⟩ := Metric.isOpen_iff.mp N₁.open_target 0 hzeroN
  let R₁ : ℝ := ε/2
  have hR₁ : 0<R₁ := half_pos hε
  have htarget₁ : Metric.closedBall (0:Schoenflies.Plane) R₁⊆N₁.target :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεtarget
  let U₁ : Set S := N₁.symm '' Metric.ball (0:Schoenflies.Plane) R₁
  have hU₁ : IsOpen U₁ := N₁.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans htarget₁)
  have ha₁U : (a 1).val∈U₁ := by
    refine ⟨0,Metric.mem_ball_self hR₁,?_⟩
    rw [←hz₁,N₁.left_inv hp₁]
  let G : Set S := ⋃ i,(c i).val.image
  have hGclosed : IsClosed G :=
    (isCompact_iUnion (fun i => isCompact_range (c i).val.embedded.continuous)).isClosed
  have hGfront : G⊆frontier F := by
    intro y hy
    rw [hfrontier]
    exact Or.inr hy
  have hfront : frontier F⊆boundaryCircle∪G := by
    intro y hy
    rw [hfrontier] at hy
    exact hy
  have hclear : ∀ t,(a t).val∉G := by
    intro t hg
    by_cases ht : t=0
    · subst t
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hg
      exact Set.disjoint_left.mp (hbaseDisjoint i) hi haB
    · exact Set.disjoint_left.mp disjoint_interior_frontier
        (hai t (bot_lt_iff_ne_bot.mpr ht)) (hGfront hg)
  obtain ⟨P,Q,M,k,hP,hQ,hPB,hQB,hPI,hQI,hPC,hQC,hdPQ,hMP,hMQ,hM₀,hM₁,hk,hk0,hk1,hkC,hkU⟩ :=
    actual_mixed_clean_connector_constructs_regional_rails_actual_caps_and_short_curve_arc
      F boundaryCircle G c₀.val.image hFclosed
      (isCompact_range c₀.val.embedded.continuous).isClosed hGclosed hc₀ hGfront hfront
      a ha hai (hActualBaseInFrontier haB) hclear hac
      N₀ N₁ η₀ η₁ hp₀ hz₀ hη₀ ht₀ (fun y hy => (hl₀ y hy).2.2.1)
      hp₁ hz₁ hη₁ ht₁ hl₁ U₀ U₁ hU₀ hU₁ (hBU₀ haB) ha₁U
  have hcap₀ : U₀⊆e.symm '' Metric.closedBall center R' :=
    Set.image_mono Metric.ball_subset_closedBall
  have hcap₁ : U₁⊆N₁.symm '' Metric.closedBall (0:Schoenflies.Plane) R₁ :=
    Set.image_mono Metric.ball_subset_closedBall
  obtain ⟨A,hA,hA0,hA1,hAI,hno⟩ :=
    hActualLooseAmbientCapsOrientedDiskExclusion F boundaryCircle c₀ hc₀
      e center R' hR' hR'target hBD N₁ 0 R₁ hR₁ htarget₁
      P Q hP hQ hPB hQB hPI hQI hPC hQC hdPQ M hMP hMQ
      (fun w => hcap₀ (hM₀ w)) (fun w => hcap₁ (hM₁ w))
      k hk hkC hk0 hk1 (fun y hy => hcap₁ (hkU hy))
  have hAF (t : Interval) (ht : t∈Set.Ioo (0:Interval) 1) : (A t).val∉frontier F :=
    fun hf => Set.disjoint_left.mp disjoint_interior_frontier (hAI t ht) hf
  refine ⟨A,hA,hA0,hA1,hAF,?_⟩
  rintro ⟨b,hb,hbB,D,hD,hboundary⟩
  have hAB (t : Interval) (ht : t∈Set.Ioo (0:Interval) 1) :
      A t∉{y : ↥F | y.val∈boundaryCircle} :=
    fun hB => hAF t ht (hActualBaseInFrontier hB)
  have hbrange : Set.range b⊆{y : ↥F | y.val∈boundaryCircle} := by
    rintro y ⟨t,rfl⟩
    exact hbB t
  have hend := actual_disk_boundary_two_arcs_forces_endpoint_orientation
    {y : ↥F | y.val∈boundaryCircle} A b hA hb hA0 hA1 hAB hbrange D hD hboundary
  exact hno b hbB hend ⟨D,hD,hboundary⟩

end CurveComplexGenusTwo.SourceTopology
