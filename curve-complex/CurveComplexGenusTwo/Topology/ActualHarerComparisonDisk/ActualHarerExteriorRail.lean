import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualStripSurfaceChart
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools
import Mathlib

open CurveComplex Set Topology Schoenflies

namespace ActualHarerComparisonGeometry

/-- An actual straight frontier segment in an embedded strip has a compact
exterior half-strip, confined to a prescribed open neighborhood. -/
theorem compact_exterior_half_strip
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (E : C(Interval × Icc (-1:ℝ) 1,S)) (hE : IsEmbedding E)
    (f : C(Interval,S)) (hcenter : ∀ t,E (t,⟨0,by norm_num⟩)=f t)
    (D A G U : Set S) (hD : IsClosed D) (hreg : D⊆closure (interior D))
    (hfront : frontier D⊆range f∪G)
    (hclear : ∀ (t:Interval) (w:Icc (-1:ℝ) 1),(w:ℝ)≠0 → E (t,w)∉A)
    (hU : IsOpen U) (hUG : Disjoint U G)
    (L R c e : Interval) (hL0 : 0<L) (hLc : L<c) (hce : c<e)
    (heR : e<R) (hR1 : R<1)
    (haxis : ∀ t∈Icc L R,f t∈frontier D∩U) :
    ∃ H : C(Interval×Interval,S),IsEmbedding H ∧ range H⊆U ∧
      (∀ t,H (t,0)=f ⟨(1-t.val)*c.val+t.val*e.val,by
        constructor <;> nlinarith [t.property.1,t.property.2,c.property.1,c.property.2,e.property.1,e.property.2]⟩) ∧
      (∀ t w:Interval,0<w → H (t,w)∉D ∧ H (t,w)∉A) ∧
      range H∩D=f '' Icc c e := by
  classical
  have hL0r : (0:ℝ)<L.val := hL0
  have hR1r : R.val<(1:ℝ) := hR1
  let z : Icc (-1:ℝ) 1 := ⟨0,by norm_num⟩
  have hprod : Icc L R ×ˢ ({z}:Set (Icc (-1:ℝ) 1))⊆E ⁻¹' U := by
    rintro ⟨t,w⟩ ⟨ht,hw⟩
    have heq : w=z := hw
    subst w
    change E (t,z)∈U
    rw [hcenter]
    exact (haxis t ht).2
  obtain ⟨V,W,_,hW,hIV,hzW,hVW⟩ := generalized_tube_lemma
    isCompact_Icc isCompact_singleton (hU.preimage E.continuous) hprod
  obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp hW z (hzW (mem_singleton z))
  let δ : ℝ := min (η/2) (1/2)
  have hδ : 0<δ := lt_min (half_pos hη) (by norm_num)
  have hδη : δ<η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδone : δ<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hband : ∀ t∈Icc L R,∀ w:Icc (-1:ℝ) 1,|(w:ℝ)|≤δ → E (t,w)∈U := by
    intro t ht w hw
    apply hVW ⟨hIV ht,hball ?_⟩
    change dist (w:ℝ) 0<η
    rw [Real.dist_eq,sub_zero]
    exact hw.trans_lt hδη
  obtain ⟨C,hCs,hCt,hcoord,hCaxis⟩ := source_embedded_strip_interior_chart E hE f hcenter
  have htarget : {x:Plane | (L:ℝ)<x 0 ∧ x 0<(R:ℝ) ∧ -δ<x 1 ∧ x 1<δ}⊆C.target := by
    intro x hx
    rw [hCt]
    exact ⟨lt_trans hL0r hx.1,lt_trans hx.2.1 hR1r,by linarith [hx.2.2.1],by linarith [hx.2.2.2]⟩
  have hpre (x:Plane) (hL:(L:ℝ)<x 0) (hR:x 0<(R:ℝ)) (hlo:-δ<x 1) (hhi:x 1<δ) :
      C.symm x=E (⟨x 0,⟨(lt_trans hL0r hL).le,(lt_trans hR hR1r).le⟩⟩,
        ⟨x 1,⟨by linarith,by linarith⟩⟩) := by
    let t : Interval := ⟨x 0,⟨(lt_trans hL0r hL).le,(lt_trans hR hR1r).le⟩⟩
    let w : Icc (-1:ℝ) 1 := ⟨x 1,⟨by linarith,by linarith⟩⟩
    have hp : E (t,w)∈C.source := by
      rw [hCs]
      exact ⟨(t,w),⟨lt_trans hL0r hL,lt_trans hR hR1r,by dsimp [w];linarith,by dsimp [w];linarith⟩,rfl⟩
    have hc : C (E (t,w))=x := by
      rw [hcoord (t,w) (lt_trans hL0r hL) (lt_trans hR hR1r) (by dsimp [w];linarith) (by dsimp [w];linarith)]
      ext k;fin_cases k <;> rfl
    exact (congrArg C.symm hc.symm).trans (C.left_inv hp)
  have hfrontier : ∀ x:Plane,(L:ℝ)<x 0 → x 0<(R:ℝ) → -δ<x 1 → x 1<δ →
      (C.symm x∈frontier D ↔ x 1=0) := by
    intro x hL hR hlo hhi
    let t : Interval := ⟨x 0,⟨(lt_trans hL0r hL).le,(lt_trans hR hR1r).le⟩⟩
    let w : Icc (-1:ℝ) 1 := ⟨x 1,⟨by linarith,by linarith⟩⟩
    have hp : C.symm x=E (t,w) := hpre x hL hR hlo hhi
    have ht : t∈Icc L R := ⟨hL.le,hR.le⟩
    have hEU : E (t,w)∈U := hband t ht w (abs_le.mpr ⟨hlo.le,hhi.le⟩)
    rw [hp]
    constructor
    · intro hx
      rcases hfront hx with ⟨u,hu⟩ | hxG
      · have he : E (t,w)=E (u,z) := hu.symm.trans (hcenter u).symm
        exact congrArg (fun p:Interval×Icc (-1:ℝ) 1 => (p.2:ℝ)) (hE.injective he)
      · exact (disjoint_left.mp hUG hEU hxG).elim
    · intro hy
      have hw : w=z := Subtype.ext hy
      rw [hw,hcenter]
      exact (haxis t ht).1
  obtain ⟨σ,hσ,hout⟩ := actual_chart_strip_exterior_half C D hD hreg L R δ
    (lt_trans hLc (lt_trans hce heR)) hδ htarget hfrontier
  have hσsq : σ*σ=1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ|=1 := by rcases hσ with rfl | rfl <;> norm_num
  let θ : Interval → Interval := fun t =>
    ⟨(1-t.val)*c.val+t.val*e.val,by
      constructor <;> nlinarith [t.property.1,t.property.2,c.property.1,c.property.2,e.property.1,e.property.2]⟩
  have hθc : Continuous θ := by fun_prop
  have hθrange (t:Interval) : θ t∈Icc c e := by
    change c.val≤(1-t.val)*c.val+t.val*e.val ∧ (1-t.val)*c.val+t.val*e.val≤e.val
    have hce' : c.val<e.val := hce
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hθbounds (t:Interval) : (L:ℝ)<(θ t:ℝ) ∧ (θ t:ℝ)<(R:ℝ) :=
    ⟨lt_of_lt_of_le hLc (hθrange t).1,lt_of_le_of_lt (hθrange t).2 heR⟩
  let w : Interval → Icc (-1:ℝ) 1 := fun u => ⟨σ*(δ/2)*u.val,by
    have hn : 0≤(δ/2)*u.val := mul_nonneg (half_pos hδ).le u.property.1
    have hu : (δ/2)*u.val≤δ/2 := mul_le_of_le_one_right (half_pos hδ).le u.property.2
    have habs : |σ*(δ/2)*u.val|≤1 := by
      rw [mul_assoc,abs_mul,hσabs,one_mul,abs_of_nonneg hn]
      linarith
    exact abs_le.mp habs⟩
  have hwc : Continuous w := by fun_prop
  have hwsmall (u:Interval) : |(w u:ℝ)|<δ := by
    change |σ*(δ/2)*u.val|<δ
    rw [mul_assoc,abs_mul,hσabs,one_mul,abs_of_nonneg (mul_nonneg (half_pos hδ).le u.property.1)]
    have hu := mul_le_of_le_one_right (half_pos hδ).le u.property.2
    linarith
  let H : C(Interval×Interval,S) := ⟨fun p => E (θ p.1,w p.2),
    E.continuous.comp ((hθc.comp continuous_fst).prodMk (hwc.comp continuous_snd))⟩
  have hθinj : Function.Injective θ := by
    intro t u he
    have hv := congrArg Subtype.val he
    apply Subtype.ext
    change (1-t.val)*c.val+t.val*e.val=(1-u.val)*c.val+u.val*e.val at hv
    have hce' : c.val<e.val := hce
    nlinarith
  have hwinj : Function.Injective w := by
    intro t u he
    have hv := congrArg Subtype.val he
    apply Subtype.ext
    change σ*(δ/2)*t.val=σ*(δ/2)*u.val at hv
    exact mul_left_cancel₀ (mul_ne_zero (by intro h; rw [h,zero_mul] at hσsq; norm_num at hσsq) (half_pos hδ).ne') hv
  have hH : IsEmbedding H := (H.continuous.isClosedEmbedding (by
    intro p v he
    have hp := hE.injective he
    exact Prod.ext (hθinj (congrArg Prod.fst hp)) (hwinj (congrArg Prod.snd hp)))).isEmbedding
  have hH0 (t) : H (t,0)=f (θ t) := by
    change E (θ t,w 0)=_
    have hw0 : w 0=z := Subtype.ext (by change σ*(δ/2)*0=0;ring)
    rw [hw0,hcenter]
  have hHout (t u:Interval) (hu:0<u) : H (t,u)∉D ∧ H (t,u)∉A := by
    have hs : 0<σ*(w u:ℝ) := by
      change 0<σ*(σ*(δ/2)*u.val)
      rw [show σ*(σ*(δ/2)*u.val)=(σ*σ)*(δ/2)*u.val from by ring,hσsq,one_mul]
      exact mul_pos (half_pos hδ) hu
    have hwne : (w u:ℝ)≠0 := by intro he;rw [he,mul_zero] at hs;exact (lt_irrefl 0) hs
    have hwlo := (abs_lt.mp (hwsmall u)).1
    have hwhi := (abs_lt.mp (hwsmall u)).2
    have hout' := (hout (Plane.mk (θ t) (w u)) (hθbounds t).1 (hθbounds t).2 hwlo hwhi hwne).mpr hs
    have hpre' := hpre (Plane.mk (θ t) (w u)) (hθbounds t).1 (hθbounds t).2 hwlo hwhi
    change C.symm (Plane.mk (θ t) (w u))=H (t,u) at hpre'
    exact ⟨hpre' ▸ hout',hclear (θ t) (w u) hwne⟩
  refine ⟨H,hH,?_,hH0,hHout,?_⟩
  · rintro x ⟨⟨t,u⟩,rfl⟩
    exact hband (θ t) ⟨(hθbounds t).1.le,(hθbounds t).2.le⟩ (w u) (hwsmall u).le
  · apply Subset.antisymm
    · rintro x ⟨⟨⟨t,u⟩,rfl⟩,hxD⟩
      have hu0 : u=0 := by
        by_contra hn
        exact (hHout t u (bot_lt_iff_ne_bot.mpr hn)).1 hxD
      subst u
      exact ⟨θ t,hθrange t,(hH0 t).symm⟩
    · rintro x ⟨v,hv,rfl⟩
      have hdiff : 0<e.val-c.val := sub_pos.mpr hce
      let t : Interval := ⟨(v.val-c.val)/(e.val-c.val),by
        constructor
        · exact div_nonneg (sub_nonneg.mpr hv.1) hdiff.le
        · exact (div_le_one hdiff).mpr (by have hve : v.val≤e.val := hv.2;linarith)⟩
      have ht : θ t=v := by
        apply Subtype.ext
        change (1-(v.val-c.val)/(e.val-c.val))*c.val+((v.val-c.val)/(e.val-c.val))*e.val=v.val
        field_simp
        ring
      refine ⟨⟨(t,0),(hH0 t).trans (congrArg f ht)⟩,?_⟩
      exact hD.frontier_subset (haxis v ⟨hLc.le.trans hv.1,hv.2.trans heR.le⟩).1

end ActualHarerComparisonGeometry
