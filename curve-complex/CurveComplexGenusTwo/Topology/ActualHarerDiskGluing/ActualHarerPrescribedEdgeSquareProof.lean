import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.CompactKernelTransport
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalDiskArcLift
import Schoenflies.JordanSchoenflies
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting

open CurveComplex Set Topology Schoenflies

namespace ActualHarerDiskGluing
set_option maxHeartbeats 4000000

theorem actual_two_side_disk_constructs_prescribed_edge_square
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (q g : C(Interval, S)) (d : C(Metric.closedBall (0 : Plane) 1, S))
    (hq : IsEmbedding q) (hg : IsEmbedding g) (hd : IsEmbedding d)
    (hzero : q 0 = g 0) (hone : q 1 = g 1)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      range q ∪ range g)
    (hcollision : ∀ s t : Interval, q s = g t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ P : C(Interval × Interval, S),
      IsEmbedding P ∧ range P = range d ∧
      (∀ t : Interval, P (t, 1) = q t) ∧
      range (fun t : Interval => P (t, 0)) ∪
        range (fun u : Interval => P (0, u)) ∪
        range (fun u : Interval => P (1, u)) = range g := by
  classical
  obtain ⟨a,b,ha,hb,hab0,hab1,habSphere,habMeet,haLift,hbLift⟩ :=
    RegionalEmbeddedFamily.clean_disk_boundary_pair_planar_lifts d hd q g hq hg
      hzero.symm hone.symm hcollision hboundary
  let top : C(Interval,Plane) :=
    ⟨fun t => Plane.mk (2*(t:ℝ)-1) 1, by fun_prop⟩
  have htinj : Function.Injective top := by
    intro s t he
    apply Subtype.ext
    have hh := congrArg (fun z : Plane => z 0) he
    change 2*(s:ℝ)-1=2*(t:ℝ)-1 at hh
    linarith
  have ht0 : top 0 = cornerNW := by ext i; fin_cases i <;> norm_num [top,Plane.mk,cornerNW]
  have ht1 : top 1 = cornerNE := by ext i; fin_cases i <;> norm_num [top,Plane.mk,cornerNE]
  have htRange : range top = sideTop := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      apply mem_sideTop.mpr
      refine ⟨rfl,abs_le.mpr ⟨?_,?_⟩⟩
      · change -1 ≤ 2*(t:ℝ)-1; linarith [t.property.1]
      · change 2*(t:ℝ)-1 ≤ 1; linarith [t.property.2]
    · intro hz
      obtain ⟨hy,hx⟩ := mem_sideTop.mp hz
      have hx' := abs_le.mp hx
      refine ⟨⟨(z 0+1)/2,⟨by linarith,by linarith⟩⟩,?_⟩
      ext i
      fin_cases i
      · change 2*((z 0+1)/2)-1=z 0
        ring
      · exact hy.symm
  have hThree : IsArcBetween (sideLeft ∪ (sideBottom ∪ sideRight)) cornerNW cornerNE := by
    apply isArcBetween_sideLeft.concatenate isArcBetween_lowerSides
    rintro z hz (hb | hr)
    · have hx := (mem_sideLeft.mp hz).1
      have hy := (mem_sideBottom.mp hb).1
      ext i
      fin_cases i
      · simpa [cornerSW] using hx
      · simpa [cornerSW] using hy
    · have hx := (mem_sideLeft.mp hz).1
      have hx' := (mem_sideRight.mp hr).1
      linarith
  obtain ⟨k,hkc,hki,hkr,hk0,hk1⟩ := hThree
  let other : C(Interval,Plane) := ⟨fun t => k t,hkc.restrict⟩
  have hoinj : Function.Injective other := by
    intro s t he
    apply Subtype.ext
    exact hki s.property t.property he
  have hoRange : range other = sideLeft ∪ (sideBottom ∪ sideRight) := by
    rw [← hkr]
    ext z
    exact ⟨fun ⟨t,ht⟩ => ⟨t,t.property,ht⟩,fun ⟨t,ht,he⟩ => ⟨⟨t,ht⟩,he⟩⟩
  have hm0 : top 0 = other 0 := ht0.trans hk0.symm
  have hm1 : top 1 = other 1 := ht1.trans hk1.symm
  have hmMeet (s t : Interval) (he : top s = other t) :
      (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
    have hzTop : top s ∈ sideTop := htRange ▸ mem_range_self s
    have hzOther : top s ∈ sideLeft ∪ (sideBottom ∪ sideRight) :=
      he.symm ▸ (hoRange ▸ mem_range_self t)
    have hend : top s = cornerNW ∨ top s = cornerNE := by
      rcases hzOther with hl | hbot | hr
      · exact Or.inl (sideTop_meet_sideLeft _ hzTop hl)
      · have hh := (mem_sideTop.mp hzTop).1
        have hh' := (mem_sideBottom.mp hbot).1
        linarith
      · right
        have hx := (mem_sideRight.mp hr).1
        have hy := (mem_sideTop.mp hzTop).1
        ext i
        fin_cases i
        · simpa [cornerNE] using hx
        · simpa [cornerNE] using hy
    rcases hend with he0 | he1
    · exact Or.inl ⟨htinj (he0.trans ht0.symm),hoinj (he.symm.trans (he0.trans hk0.symm))⟩
    · exact Or.inr ⟨htinj (he1.trans ht1.symm),hoinj (he.symm.trans (he1.trans hk1.symm))⟩
  have hmCover : range top ∪ range other = modelCurve := by
    rw [htRange,hoRange,modelCurve_eq_sides]
    ext z
    simp only [mem_union]
    tauto
  let m : C(Interval ⊕ Interval, modelCurve) :=
    ⟨fun x => ⟨Sum.elim top other x, by
      cases x with
      | inl t => exact hmCover ▸ Or.inl (mem_range_self t)
      | inr t => exact hmCover ▸ Or.inr (mem_range_self t)⟩,
      by fun_prop⟩
  let n : C(Interval ⊕ Interval, Metric.sphere (0 : Plane) 1) :=
    ⟨fun x => ⟨Sum.elim a b x, by
      cases x with
      | inl t => exact habSphere ▸ Or.inl (mem_range_self t)
      | inr t => exact habSphere ▸ Or.inr (mem_range_self t)⟩,
      by fun_prop⟩
  have hms : Function.Surjective m := by
    intro z
    have hz : z.val ∈ range top ∪ range other := hmCover.symm ▸ z.property
    rcases hz with ⟨t,ht⟩ | ⟨t,ht⟩
    · exact ⟨Sum.inl t,Subtype.ext ht⟩
    · exact ⟨Sum.inr t,Subtype.ext ht⟩
  have hns : Function.Surjective n := by
    intro z
    have hz : z.val ∈ range a ∪ range b := habSphere.symm ▸ z.property
    rcases hz with ⟨t,ht⟩ | ⟨t,ht⟩
    · exact ⟨Sum.inl t,Subtype.ext ht⟩
    · exact ⟨Sum.inr t,Subtype.ext ht⟩
  have hkernel (x y : Interval ⊕ Interval) : m x = m y ↔ n x = n y := by
    simpa only [m,n,ContinuousMap.coe_mk,Subtype.mk.injEq] using
      clean_pair_sum_kernel top other a b htinj hoinj ha.injective hb.injective
        hm0 hm1 hab0 hab1 hmMeet habMeet x y
  obtain ⟨f,hf,hfr,hfe⟩ := compact_kernel_transport m n hms hkernel
  have : CompactSpace modelCurve := isCompact_iff_compactSpace.mp isCompact_modelCurve
  let e : modelCurve ≃ₜ Metric.sphere (0 : Plane) 1 :=
    f.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f
      ⟨hf.injective, by
        intro z
        obtain ⟨x,hx⟩ := hns z
        exact ⟨m x,(hfe x).trans hx⟩⟩)
  obtain ⟨F,hF⟩ := jordan_schoenflies_of_homeomorph isJordanCurve_modelCurve
    RegionalEmbeddedFamily.unit_sphere_isJordanCurve e
  have hFt (t : Interval) : F (top t) = a t :=
    (hF (m (Sum.inl t))).trans (congrArg Subtype.val (hfe (Sum.inl t)))
  have hFo (t : Interval) : F (other t) = b t :=
    (hF (m (Sum.inr t))).trans (congrArg Subtype.val (hfe (Sum.inr t)))
  have hFsphere : F '' modelCurve = Metric.sphere (0 : Plane) 1 := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hF ⟨x,hx⟩]
      exact (e ⟨x,hx⟩).property
    · intro hz
      refine ⟨e.symm ⟨z,hz⟩,(e.symm ⟨z,hz⟩).property,?_⟩
      rw [hF (e.symm ⟨z,hz⟩)]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
  have hFclosed : F '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
    rw [← LocalSurgery.actualModelSquareClosedRegion, image_union,hFsphere,
      CurveComplex.jordan_inside_homeomorph_image,hFsphere,
      RegionalEmbeddedFamily.inside_unit_sphere,union_comm,Metric.ball_union_sphere]
  let sq : C(Interval × Interval, Plane) :=
    ⟨fun z => Plane.mk (2*(z.1:ℝ)-1) (2*(z.2:ℝ)-1),by fun_prop⟩
  have hsqi : Function.Injective sq := by
    intro x y he
    apply Prod.ext <;> apply Subtype.ext
    · have hh := congrArg (fun z : Plane => z 0) he
      change 2*(x.1:ℝ)-1=2*(y.1:ℝ)-1 at hh
      linarith
    · have hh := congrArg (fun z : Plane => z 1) he
      change 2*(x.2:ℝ)-1=2*(y.2:ℝ)-1 at hh
      linarith
  have hsqr : range sq = Plane.closedSquare 0 1 := by
    ext z
    rw [Plane.closedSquare_eq_inter]
    simp only [mem_inter_iff,mem_setOf_eq]
    norm_num only [PiLp.zero_apply, WithLp.ofLp_zero, Pi.zero_apply, zero_sub,zero_add]
    constructor
    · rintro ⟨t,rfl⟩
      change (-1 ≤ 2*(t.1:ℝ)-1 ∧ 2*(t.1:ℝ)-1 ≤ 1) ∧
        (-1 ≤ 2*(t.2:ℝ)-1 ∧ 2*(t.2:ℝ)-1 ≤ 1)
      constructor <;> constructor <;> linarith [t.1.property.1,t.1.property.2,t.2.property.1,t.2.property.2]
    · rintro ⟨⟨hx0,hx1⟩,hy0,hy1⟩
      change -1 ≤ z 0 at hx0
      change z 0 ≤ 1 at hx1
      change -1 ≤ z 1 at hy0
      change z 1 ≤ 1 at hy1
      refine ⟨(⟨(z 0+1)/2,⟨by linarith,by linarith⟩⟩,
        ⟨(z 1+1)/2,⟨by linarith,by linarith⟩⟩),?_⟩
      ext i
      fin_cases i <;> dsimp [sq,Plane.mk] <;> ring
  let L : C(Interval × Interval,Metric.closedBall (0 : Plane) 1) :=
    ⟨fun x => ⟨F (sq x),hFclosed ▸ mem_image_of_mem F (hsqr ▸ mem_range_self x)⟩,
      (F.continuous.comp sq.continuous).subtype_mk _⟩
  have hLi : Function.Injective L := fun x y h => hsqi (F.injective (congrArg Subtype.val h))
  have hLs : Function.Surjective L := by
    intro z
    obtain ⟨x,hx,he⟩ : z.val ∈ F '' Plane.closedSquare 0 1 := hFclosed.symm ▸ z.property
    obtain ⟨t,rfl⟩ := hsqr.symm ▸ hx
    exact ⟨t,Subtype.ext he⟩
  let P := d.comp L
  have hPt (t : Interval) : P (t,1) = q t := by
    obtain ⟨z,hz,hdz⟩ := haLift t
    apply Eq.trans _ hdz
    apply congrArg d
    apply Subtype.ext
    change F (sq (t,1))=z.val
    have he : sq (t,1)=top t := by ext i; fin_cases i <;> norm_num [sq,top,Plane.mk]
    rw [he,hFt,hz]
  have hOtherPre :
      range (fun t : Interval => sq (t,0)) ∪
      range (fun u : Interval => sq (0,u)) ∪
      range (fun u : Interval => sq (1,u)) = range other := by
    rw [hoRange]
    have heH (y : ℝ) : range (fun t : Interval => Plane.mk (2*(t:ℝ)-1) y) =
        {z : Plane | z 1=y ∧ |z 0|≤1} := by
      ext z
      constructor
      · rintro ⟨t,rfl⟩
        refine ⟨rfl,abs_le.mpr ⟨?_,?_⟩⟩
        · change -1 ≤ 2*(t:ℝ)-1; linarith [t.property.1]
        · change 2*(t:ℝ)-1 ≤ 1; linarith [t.property.2]
      · rintro ⟨hy,hx⟩
        have hx' := abs_le.mp hx
        refine ⟨⟨(z 0+1)/2,⟨by linarith,by linarith⟩⟩,?_⟩
        ext i; fin_cases i
        · change 2*((z 0+1)/2)-1=z 0; ring
        · exact hy.symm
    have heV (x : ℝ) : range (fun u : Interval => Plane.mk x (2*(u:ℝ)-1)) =
        {z : Plane | z 0=x ∧ |z 1|≤1} := by
      ext z
      constructor
      · rintro ⟨t,rfl⟩
        refine ⟨rfl,abs_le.mpr ⟨?_,?_⟩⟩
        · change -1 ≤ 2*(t:ℝ)-1; linarith [t.property.1]
        · change 2*(t:ℝ)-1 ≤ 1; linarith [t.property.2]
      · rintro ⟨hx,hy⟩
        have hy' := abs_le.mp hy
        refine ⟨⟨(z 1+1)/2,⟨by linarith,by linarith⟩⟩,?_⟩
        ext i; fin_cases i
        · exact hx.symm
        · change 2*((z 1+1)/2)-1=z 1; ring
    have h0 : (0 : Interval).val=0 := rfl
    have h1 : (1 : Interval).val=1 := rfl
    simp only [sq,ContinuousMap.coe_mk,h0,h1,mul_zero,mul_one,zero_sub]
    norm_num only [show (2:ℝ)-1=1 by norm_num]
    rw [heH,heV,heV]
    ext z
    simp only [mem_union,mem_setOf_eq,mem_sideBottom,mem_sideLeft,mem_sideRight]
    tauto
  refine ⟨P,hd.comp (L.continuous.isClosedEmbedding hLi).isEmbedding,?_,hPt,?_⟩
  · change range (d ∘ L)=range d
    exact hLs.range_comp d
  · have hRangeF : F '' range other = range b := by
      rw [← range_comp]
      congr 1
      funext t
      exact hFo t
    have hRangeEdges :
        range (fun t : Interval => F (sq (t,0))) ∪
        range (fun u : Interval => F (sq (0,u))) ∪
        range (fun u : Interval => F (sq (1,u))) = range b := by
      change range (F ∘ (fun t : Interval => sq (t,0))) ∪
        range (F ∘ (fun u : Interval => sq (0,u))) ∪
        range (F ∘ (fun u : Interval => sq (1,u))) = range b
      rw [range_comp,range_comp,range_comp,← image_union,← image_union,hOtherPre,hRangeF]
    have hPfrom (z : Interval × Interval) (hm : F (sq z) ∈ range b) :
        P z ∈ range g := by
      obtain ⟨v,hv⟩ := hm
      obtain ⟨w,hw,he⟩ := hbLift v
      exact ⟨v,he.symm.trans (congrArg d (Subtype.ext (hw.trans hv)))⟩
    ext x
    constructor
    · rintro ((⟨t,rfl⟩ | ⟨u,rfl⟩) | ⟨u,rfl⟩)
      · apply hPfrom
        rw [← hRangeEdges]
        exact Or.inl (Or.inl (mem_range_self t))
      · apply hPfrom
        rw [← hRangeEdges]
        exact Or.inl (Or.inr (mem_range_self u))
      · apply hPfrom
        rw [← hRangeEdges]
        exact Or.inr (mem_range_self u)
    · rintro ⟨v,rfl⟩
      have hm : b v ∈ range (fun t : Interval => F (sq (t,0))) ∪
          range (fun u : Interval => F (sq (0,u))) ∪
          range (fun u : Interval => F (sq (1,u))) := hRangeEdges.symm ▸ mem_range_self v
      obtain ⟨z,hz,he⟩ := hbLift v
      rcases hm with (⟨t,ht⟩ | ⟨u,hu⟩) | ⟨u,hu⟩
      · exact Or.inl (Or.inl ⟨t,(congrArg d (Subtype.ext (ht.trans hz.symm))).trans he⟩)
      · exact Or.inl (Or.inr ⟨u,(congrArg d (Subtype.ext (hu.trans hz.symm))).trans he⟩)
      · exact Or.inr ⟨u,(congrArg d (Subtype.ext (hu.trans hz.symm))).trans he⟩

end ActualHarerDiskGluing
