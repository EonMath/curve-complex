import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualInitialAxisPortImage
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnFramedStrips
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies
/-- Actual coordinate access along an embedded source arc near an internal
axis port. Both source parameter and chart coordinates are produced by IVT;
no coordinate inverse or access segment is an input. -/
theorem source_internal_axis_port_coordinate_access
    {S : Type} [TopologicalSpace S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (E : OpenPartialHomeomorph S Plane) (θ : Interval) (η : ℝ)
    (hθ : 0<(θ:ℝ) ∧ (θ:ℝ)<1) (hη : 0<η)
    (hlocal : ∀ u : Interval, |(u:ℝ)-(θ:ℝ)|<η →
      f u ∈ E.source ∧ E (f u) 0=0) :
    ∃ r : ℝ, 0<r ∧ ∀ y : ℝ, |y-E (f θ) 1|<r →
      ∃ u : Interval, 0<(u:ℝ) ∧ (u:ℝ)<1 ∧
        |(u:ℝ)-(θ:ℝ)|<η ∧ E (f u)=Plane.mk 0 y := by
  let ε : ℝ := min (θ:ℝ) (min (1-(θ:ℝ)) η)/2
  have hε : 0<ε := div_pos (lt_min hθ.1 (lt_min (by linarith [hθ.2]) hη)) (by norm_num)
  have hεθ : ε≤(θ:ℝ)/2 := by
    have h := min_le_left (θ:ℝ) (min (1-(θ:ℝ)) η)
    dsimp [ε]
    linarith
  have hε1 : ε≤(1-(θ:ℝ))/2 := by
    have h := (min_le_right (θ:ℝ) (min (1-(θ:ℝ)) η)).trans (min_le_left _ _)
    dsimp [ε]
    linarith
  have hεη : ε≤η/2 := by
    have h := (min_le_right (θ:ℝ) (min (1-(θ:ℝ)) η)).trans (min_le_right _ _)
    dsimp [ε]
    linarith
  let L : Interval := ⟨(θ:ℝ)-ε,by constructor <;> linarith [θ.property.1,θ.property.2]⟩
  let R : Interval := ⟨(θ:ℝ)+ε,by constructor <;> linarith [θ.property.1,θ.property.2]⟩
  have hLR : (L:ℝ)<R := by change (θ:ℝ)-ε<(θ:ℝ)+ε; linarith
  obtain ⟨q,hq,hq0,hq1,hqrange,hqval⟩ := source_affine_subinterval L R hLR
  have hqI (t : Interval) : L≤q t ∧ q t≤R := by
    have hh : q t ∈ Set.Icc L R := hqrange ▸ Set.mem_range_self t
    exact hh
  have hnear (t : Interval) : |(q t:ℝ)-(θ:ℝ)|<η := by
    have hlo : (θ:ℝ)-ε≤(q t:ℝ) := (hqI t).1
    have hhi : (q t:ℝ)≤(θ:ℝ)+ε := (hqI t).2
    rw [abs_lt]
    constructor <;> linarith
  have hlocalq (t : Interval) := hlocal (q t) (hnear t)
  let z : C(Interval,ℝ) := ⟨fun t=>E (f (q t)) 1,by
    apply continuous_iff_continuousAt.mpr
    intro t
    have heval : Continuous (fun y : Plane=>y 1) := by fun_prop
    exact heval.continuousAt.comp
      ((E.continuousAt (hlocalq t).1).comp (f := fun u=>f (q u))
        (f.continuous.comp q.continuous).continuousAt)⟩
  have hzi : Function.Injective z := by
    intro t u he
    apply hq.injective
    apply hf.injective
    apply E.injOn (hlocalq t).1 (hlocalq u).1
    ext j
    fin_cases j
    · exact (hlocalq t).2.trans (hlocalq u).2.symm
    · exact he
  have hθI : θ ∈ Set.Icc L R := by
    change (θ:ℝ)-ε≤(θ:ℝ) ∧ (θ:ℝ)≤(θ:ℝ)+ε
    constructor <;> linarith
  obtain ⟨tθ,htθ⟩ := hqrange.symm ▸ hθI
  have htθmid : (tθ:ℝ)=1/2 := by
    have hh := hqval tθ
    rw [htθ] at hh
    change (θ:ℝ)=(θ:ℝ)-ε+((θ:ℝ)+ε-((θ:ℝ)-ε))*(tθ:ℝ) at hh
    nlinarith
  have htθ0 : (0:Interval)<tθ := by change 0<(tθ:ℝ); rw [htθmid]; norm_num
  have htθ1 : tθ<(1:Interval) := by change (tθ:ℝ)<1; rw [htθmid]; norm_num
  have hzθ : z tθ=E (f θ) 1 := by change E (f (q tθ)) 1=_; rw [htθ]
  have hbetween : min (z 0) (z 1)<z tθ ∧ z tθ< max (z 0) (z 1) := by
    rcases z.continuous.strictMono_of_inj_boundedOrder' hzi with hm|hm
    · have h01 := hm (by norm_num : (0:Interval)<1)
      rw [min_eq_left h01.le,max_eq_right h01.le]
      exact ⟨hm htθ0,hm htθ1⟩
    · have h01 := hm (by norm_num : (0:Interval)<1)
      rw [min_eq_right h01.le,max_eq_left h01.le]
      exact ⟨hm htθ1,hm htθ0⟩
  let r : ℝ := min (z tθ-min (z 0) (z 1)) (max (z 0) (z 1)-z tθ)
  have hr : 0<r := lt_min (sub_pos.mpr hbetween.1) (sub_pos.mpr hbetween.2)
  refine ⟨r,hr,?_⟩
  intro y hy
  rw [← hzθ,abs_lt] at hy
  have hyrange : y ∈ Set.Icc (min (z 0) (z 1)) (max (z 0) (z 1)) := by
    have hleft : r≤z tθ-min (z 0) (z 1) := min_le_left _ _
    have hright : r≤ max (z 0) (z 1)-z tθ := min_le_right _ _
    constructor <;> linarith [hy.1,hy.2]
  have hyimage : y ∈ z '' Set.Icc (0:Interval) 1 := by
    by_cases horder : z 0≤z 1
    · apply intermediate_value_Icc (by norm_num : (0:Interval)≤1) z.continuous.continuousOn
      simpa only [min_eq_left horder,max_eq_right horder] using hyrange
    · apply intermediate_value_Icc' (by norm_num : (0:Interval)≤1) z.continuous.continuousOn
      simpa only [min_eq_right (le_of_not_ge horder),max_eq_left (le_of_not_ge horder)] using hyrange
  obtain ⟨t,_ht,ht⟩ := hyimage
  refine ⟨q t,?_,?_,hnear t,?_⟩
  · have hh : (θ:ℝ)-ε≤(q t:ℝ) := (hqI t).1
    linarith
  · have hh : (q t:ℝ)≤(θ:ℝ)+ε := (hqI t).2
    linarith
  · ext j
    fin_cases j
    · exact (hlocalq t).2
    · exact ht
end CurveComplex

#print axioms CurveComplex.source_internal_axis_port_coordinate_access
