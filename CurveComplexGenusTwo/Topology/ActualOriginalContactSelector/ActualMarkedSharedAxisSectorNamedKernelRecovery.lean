import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualNegativeInternalMeshNodeIncidenceKernelRecovery
import CurveComplexGenusTwo.Filtration.ActualFiltrationEndpointProgress
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import Mathlib.Topology.Subpath
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace CurveComplex.HyperellipticModel.H1ActualMarkedSectorKernel
open Set Topology CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actualIntervalSignConstant (g : C(Interval,ℝ))
    (x y s t : Interval) (hs : s ∈ Set.Ioo x y) (ht : t ∈ Set.Ioo x y)
    (hn : ∀ z, x < z → z < y → g z ≠ 0) :
    g s < 0 ↔ g t < 0 := by
  constructor
  · intro h
    exact lt_of_le_of_ne (CurveComplex.LocalSurgery.actualNoZeroIntervalSign g x y s hs.1 hs.2 h hn t
      ⟨ht.1.le,ht.2.le⟩) (hn t ht.1 ht.2)
  · intro h
    exact lt_of_le_of_ne (CurveComplex.LocalSurgery.actualNoZeroIntervalSign g x y t ht.1 ht.2 h hn s
      ⟨hs.1.le,hs.2.le⟩) (hn s hs.1 hs.2)

variable (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
theorem actualMarkedSharedAxisChartsSameSide (p : S)
    (hp : p ∈ a.val.image) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
    (hpC : p ∈ C.source) (hpD : p ∈ D.source)
    (hC : ∀ x ∈ C.source, x ∈ a.val.image ↔ (C x).1 = 0)
    (hD : ∀ x ∈ D.source, x ∈ a.val.image ↔ (D x).1 = 0) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ C.source ∩ D.source ∧
      ∀ x ∈ U, ∀ y ∈ U, x ∉ a.val.image → y ∉ a.val.image →
        (((C x).1 < 0 ↔ (C y).1 < 0) ↔
          ((D x).1 < 0 ↔ (D y).1 < 0)) := by
  classical
  have hCp : (C p).1 = 0 := (hC p hpC).mp hp
  have hDp : (D p).1 = 0 := (hD p hpD).mp hp
  let P := C.trans (Homeomorph.addRight (-C p)).toOpenPartialHomeomorph
  let Q := D.trans (Homeomorph.addRight (-D p)).toOpenPartialHomeomorph
  have hPs : P.source = C.source := by
    ext x
    simp only [P,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
  have hQs : Q.source = D.source := by
    ext x
    simp only [Q,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
  have hPf (x : S) : (P x).1 = (C x).1 := by
    change (C x).1 + -(C p).1 = (C x).1
    rw [hCp]
    simp
  have hQf (x : S) : (Q x).1 = (D x).1 := by
    change (D x).1 + -(D p).1 = (D x).1
    rw [hDp]
    simp
  have hPp : P p = (0,0) := by
    change C p + -C p = (0,0)
    exact add_neg_cancel _
  have hQp : Q p = (0,0) := by
    change D p + -D p = (0,0)
    exact add_neg_cancel _
  have hpP : p ∈ P.source := hPs.symm ▸ hpC
  have hpQ : p ∈ Q.source := hQs.symm ▸ hpD
  let T := P.symm.trans Q
  have hTs : (0,0) ∈ T.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hPp ▸ P.map_source hpP,?_⟩
    change P.symm (0,0) ∈ Q.source
    rw [←hPp,P.left_inv hpP]
    exact hpQ
  have hT0 : T (0,0) = (0,0) := by
    change Q (P.symm (0,0)) = (0,0)
    rw [←hPp,P.left_inv hpP]
    exact hQp.trans hPp.symm
  have hTa (z : ℝ × ℝ) (hz : z ∈ T.source) : z.1 = 0 ↔ (T z).1 = 0 := by
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hPinv := P.right_inv hz.1
    have hPaxis : P.symm z ∈ a.val.image ↔ z.1 = 0 := by
      have hh := hC (P.symm z) (hPs ▸ P.symm.map_source hz.1)
      rw [←hPf (P.symm z),hPinv] at hh
      exact hh
    have hQaxis : P.symm z ∈ a.val.image ↔ (Q (P.symm z)).1 = 0 := by
      rw [hQf]
      exact hD (P.symm z) (hQs ▸ hz.2)
    exact hPaxis.symm.trans hQaxis
  obtain ⟨r,hr,hball,ε,hrelative⟩ :=
    CurveComplex.LocalSurgery.local_axis_transition_side_constant T hTs hT0 hTa
  let U := Q.source ∩ (P.source ∩ P ⁻¹' Metric.ball (0,0) r)
  have hUopen : IsOpen U := Q.open_source.inter
    (P.isOpen_inter_preimage Metric.isOpen_ball)
  have hpU : p ∈ U := ⟨hpQ,hpP,by
    change P p ∈ Metric.ball (0,0) r
    rw [hPp]
    exact Metric.mem_ball_self hr⟩
  have hsub : U ⊆ C.source ∩ D.source := fun _ hx => ⟨hPs ▸ hx.2.1,hQs ▸ hx.1⟩
  have hlabel (x : S) (hx : x ∈ U) (hxb : x ∉ a.val.image) :
      (if 0 < (D x).1 then (1 : ZMod 2) else 0) =
        (if 0 < (C x).1 then (1 : ZMod 2) else 0) + ε := by
    have hn : (P x).1 ≠ 0 := by
      rw [hPf]
      exact fun hh => hxb ((hC x (hPs ▸ hx.2.1)).mpr hh)
    have hh := hrelative (P x) hx.2.2 hn
    have htrans : T (P x) = Q x := by
      change Q (P.symm (P x)) = Q x
      rw [P.left_inv hx.2.1]
    simpa only [htrans,hPf,hQf] using hh
  refine ⟨U,hUopen,hpU,hsub,?_⟩
  intro x hx y hy hxb hyb
  have hxnC : (C x).1 ≠ 0 := fun hh => hxb ((hC x (hsub hx).1).mpr hh)
  have hynC : (C y).1 ≠ 0 := fun hh => hyb ((hC y (hsub hy).1).mpr hh)
  have hxnD : (D x).1 ≠ 0 := fun hh => hxb ((hD x (hsub hx).2).mpr hh)
  have hynD : (D y).1 ≠ 0 := fun hh => hyb ((hD y (hsub hy).2).mpr hh)
  have hlabels :
      ((if 0 < (D x).1 then (1 : ZMod 2) else 0) =
        (if 0 < (D y).1 then (1 : ZMod 2) else 0)) ↔
      ((if 0 < (C x).1 then (1 : ZMod 2) else 0) =
        (if 0 < (C y).1 then (1 : ZMod 2) else 0)) := by
    rw [hlabel x hx hxb,hlabel y hy hyb]
    exact add_right_cancel_iff
  by_cases hcx : 0 < (C x).1 <;> by_cases hcy : 0 < (C y).1 <;>
    by_cases hdx : 0 < (D x).1 <;> by_cases hdy : 0 < (D y).1
  all_goals simp only [hcx,hcy,hdx,hdy,ite_true,ite_false] at hlabels
  all_goals have hcnegx : (C x).1 < 0 ↔ ¬0 < (C x).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hxnC⟩
  all_goals have hcnegy : (C y).1 < 0 ↔ ¬0 < (C y).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hynC⟩
  all_goals have hdnegx : (D x).1 < 0 ↔ ¬0 < (D x).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hxnD⟩
  all_goals have hdnegy : (D y).1 < 0 ↔ ¬0 < (D y).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hynD⟩
  all_goals rw [hcnegx,hcnegy,hdnegx,hdnegy]
  all_goals norm_num at hlabels
  all_goals simp only [hcx,hcy,hdx,hdy,not_true_eq_false,not_false_eq_true,
    iff_self,iff_true,iff_false,true_iff,false_iff]
theorem actualMarkedSharedAxisTraceSameSectorSign
    (γ : C(Interval,S)) (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
    (hroot : γ u ∈ a.val.image) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
    (hpC : γ u ∈ C.source) (hpD : γ u ∈ D.source)
    (hC : ∀ x ∈ C.source, x ∈ a.val.image ↔ (C x).1 = 0)
    (hD : ∀ x ∈ D.source, x ∈ a.val.image ↔ (D x).1 = 0)
    (g h : C(Interval,ℝ)) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hg : ∀ t, g t = (C (γ t)).1/c) (hh : ∀ t, h t = (D (γ t)).1/d)
    (x y sl sr X Y sL sR : Interval)
    (hxu : x < u) (huy : u < y) (hXu : X < u) (huY : u < Y)
    (hsl : sl ∈ Set.Ioo x u) (hsr : sr ∈ Set.Ioo u y)
    (hsL : sL ∈ Set.Ioo X u) (hsR : sR ∈ Set.Ioo u Y)
    (hgl : ∀ t, x < t → t < u → g t ≠ 0)
    (hgr : ∀ t, u < t → t < y → g t ≠ 0)
    (hhl : ∀ t, X < t → t < u → h t ≠ 0)
    (hhr : ∀ t, u < t → t < Y → h t ≠ 0) :
    ((g sl < 0 ↔ g sr < 0) ↔ (h sL < 0 ↔ h sR < 0)) := by
  obtain ⟨U,hUopen,hpU,hUcharts,hside⟩ :=
    actualMarkedSharedAxisChartsSameSide M a (γ u) hroot C D hpC hpD hC hD
  let realγ := CurveComplex.LocalSurgery.realIntervalPath γ
  have hreal (t : Interval) : realγ t.val = γ t := by
    change γ (Set.projIcc 0 1 (by norm_num) t.val) = γ t
    rw [Set.projIcc_of_mem _ t.property]
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp
    (realγ.continuous.continuousAt.preimage_mem_nhds
      (hUopen.mem_nhds (hreal u ▸ hpU)))
  have hlo : max (max x.val X.val) (u.val-δ/2) < u.val := by
    apply max_lt
    · exact max_lt (show x.val < u.val from hxu) (show X.val < u.val from hXu)
    · linarith
  obtain ⟨v,hv0,hv1⟩ := exists_between hlo
  have hvx : x.val < v := (le_max_left x.val X.val).trans
    (le_max_left _ _) |>.trans_lt hv0
  have hvX : X.val < v := (le_max_right x.val X.val).trans
    (le_max_left _ _) |>.trans_lt hv0
  let vI : Interval := ⟨v,⟨x.property.1.trans hvx.le,hv1.le.trans u.property.2⟩⟩
  have hhi : u.val < min (min y.val Y.val) (u.val+δ/2) := by
    apply lt_min
    · exact lt_min (show u.val < y.val from huy) (show u.val < Y.val from huY)
    · linarith
  obtain ⟨w,hw0,hw1⟩ := exists_between hhi
  have hwy : w < y.val := hw1.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hwY : w < Y.val := hw1.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  let wI : Interval := ⟨w,⟨u.property.1.trans hw0.le,hwy.le.trans y.property.2⟩⟩
  have hvU : γ vI ∈ U := by
    rw [←hreal vI]
    apply hδU
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    have hl := (le_max_right _ _).trans_lt hv0
    constructor <;> change _ < _ <;> linarith
  have hwU : γ wI ∈ U := by
    rw [←hreal wI]
    apply hδU
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    have hh' := hw1.trans_le (min_le_right _ _)
    constructor <;> change _ < _ <;> linarith
  have hgv : g vI ≠ 0 := hgl vI hvx hv1
  have hgw : g wI ≠ 0 := hgr wI hw0 hwy
  have hhv : h vI ≠ 0 := hhl vI hvX hv1
  have hhw : h wI ≠ 0 := hhr wI hw0 hwY
  have hCv : (C (γ vI)).1 ≠ 0 := by
    intro he
    apply hgv
    rw [hg vI,he,zero_div]
  have hCw : (C (γ wI)).1 ≠ 0 := by
    intro he
    apply hgw
    rw [hg wI,he,zero_div]
  have hDv : (D (γ vI)).1 ≠ 0 := by
    intro he
    apply hhv
    rw [hh vI,he,zero_div]
  have hDw : (D (γ wI)).1 ≠ 0 := by
    intro he
    apply hhw
    rw [hh wI,he,zero_div]
  have hvb : γ vI ∉ a.val.image := fun he => hCv ((hC _ (hUcharts hvU).1).mp he)
  have hwb : γ wI ∉ a.val.image := fun he => hCw ((hC _ (hUcharts hwU).1).mp he)
  have hsamples : ((g vI < 0 ↔ g wI < 0) ↔ (h vI < 0 ↔ h wI < 0)) := by
    rw [hg vI,hg wI,hh vI,hh wI]
    exact (CurveComplex.LocalSurgery.normalized_axis_same_sign _ _ c hCv hCw hc).trans
      ((hside _ hvU _ hwU hvb hwb).trans
        (CurveComplex.LocalSurgery.normalized_axis_same_sign _ _ d hDv hDw hd).symm)
  have hl := actualIntervalSignConstant g x u sl vI hsl ⟨hvx,hv1⟩ hgl
  have hr := actualIntervalSignConstant g u y sr wI hsr ⟨hw0,hwy⟩ hgr
  have hL := actualIntervalSignConstant h X u sL vI hsL ⟨hvX,hv1⟩ hhl
  have hR := actualIntervalSignConstant h u Y sR wI hsR ⟨hw0,hwY⟩ hhr
  rwa [←hl,←hr,←hL,←hR] at hsamples

#print axioms actualMarkedSharedAxisTraceSameSectorSign
end CurveComplex.HyperellipticModel.H1ActualMarkedSectorKernel
