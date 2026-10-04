import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14RegularSegmentSourceReadOnly
import Mathlib.Topology.Order.IntermediateValue
import CurveComplexGenusTwo.Dictionary.Circle24.ActualVerticalAnnulusBoundary
import Mathlib.Analysis.Convex.GaugeRescale
import CurveComplexGenusTwo.Dictionary.Circle24.OneMarkCellQuotient
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open scoped Manifold ContDiff
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]

set_option maxHeartbeats 12000000 in
theorem actual_nonloop_regular_neighborhood_lift_core_annulus
    (M : HyperellipticModel E S) (a : NonLoopArc M)
    (N : ArcNeighborhood a)
    (pair : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ N.closedSet)
    (hcore : (fun z => (pair z : S)) '' ClassificationSchoenflies.standardArcCore = a.image) :
    ∃ H : Circle × Interval ≃ₜ M.cover.projection ⁻¹' N.closedSet,
      Set.range (fun z : Circle => (H (z,⟨1/2,by norm_num⟩)).val) =
        M.cover.projection ⁻¹' a.image ∧
      Set.range (fun z : Circle => (H (z,0)).val) ∪
        Set.range (fun z : Circle => (H (z,1)).val) =
        M.cover.projection ⁻¹' N.boundary.image := by
  classical
  have hzero : (0 : Interval) = ⟨0,by norm_num⟩ := by apply Subtype.ext; norm_num
  have hone : (1 : Interval) = ⟨1,by norm_num⟩ := by apply Subtype.ext; norm_num
  let A : Interval → N.closedSet := fun t =>
    ⟨a.val.map t, interior_subset (N.arc_inside ⟨t,rfl⟩)⟩
  have hA : Continuous A := a.val.continuous.subtype_mk _
  let c : Interval → Metric.closedBall (0 : Plane) 1 := pair.symm ∘ A
  have hc : Continuous c := pair.symm.continuous.comp hA
  have hcCore (t) : c t ∈ ClassificationSchoenflies.standardArcCore := by
    have ht : a.val.map t ∈ a.image := ⟨t,rfl⟩
    rw [← hcore] at ht
    obtain ⟨z,hz,he⟩ := ht
    have hp : pair z = A t := Subtype.ext he
    change pair.symm (A t) ∈ _
    rw [← hp,pair.symm_apply_apply]
    exact hz
  let g : Interval → ℝ := fun t => (c t).val 0
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hginj : Function.Injective g := by
    intro t u he
    have hz : c t = c u := by
      apply Subtype.ext
      ext i
      fin_cases i
      · exact he
      · exact (hcCore t).2.1.trans (hcCore u).2.1.symm
    apply a.injective
    have hp := congrArg (fun z => (pair z : S)) hz
    simpa only [c,Function.comp_apply,pair.apply_symm_apply,A] using hp
  have hgrange : range g = Icc (-1/2 : ℝ) (1/2) := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      simpa only [g,neg_div,Set.mem_Icc] using abs_le.mp (hcCore t).2.2
    · intro hx
      let z : Plane := WithLp.toLp 2 ![x,0]
      have hnorm : ‖z‖ = |x| := by
        have hsq : ‖z‖ ^ 2 = x^2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          norm_num [z,Fin.sum_univ_two]
        nlinarith [norm_nonneg z, abs_nonneg x, sq_abs x]
      let zd : Metric.closedBall (0 : Plane) 1 := ⟨z,by
        simpa only [Metric.mem_closedBall,dist_zero_right,hnorm] using
          (show |x| ≤ 1 by have h := abs_le.mpr (show -(1/2 : ℝ) ≤ x ∧ x ≤ 1/2 by simpa only [neg_div,Set.mem_Icc] using hx); linarith)⟩
      have hz : zd ∈ ClassificationSchoenflies.standardArcCore := by
        exact ⟨zd.property,by simp [zd,z],by simpa [zd,z] using abs_le.mpr (show -(1/2 : ℝ) ≤ x ∧ x ≤ 1/2 by simpa only [neg_div,Set.mem_Icc] using hx)⟩
      have hp : (pair zd : S) ∈ a.image := hcore ▸ ⟨zd,hz,rfl⟩
      obtain ⟨t,ht⟩ := hp
      refine ⟨t,?_⟩
      have hpair : pair zd = A t := Subtype.ext ht.symm
      change (pair.symm (A t)).val 0 = x
      rw [← hpair,pair.symm_apply_apply]
      rfl
  have hcoordinateEnds :
      ({g 0,g 1} : Set ℝ) = {(-1/2 : ℝ),1/2} := by
    have hzero := hgrange ▸ Set.mem_range_self 0 (f:=g)
    have hone := hgrange ▸ Set.mem_range_self 1 (f:=g)
    obtain ⟨t,ht⟩ : (-1/2 : ℝ) ∈ range g := hgrange.symm ▸ (by norm_num)
    obtain ⟨u,hu⟩ : (1/2 : ℝ) ∈ range g := hgrange.symm ▸ (by norm_num)
    rcases hg.strictMono_of_inj hginj with hmono | hanti
    · have hl := hmono.monotone (show (0:Interval) ≤ t from t.property.1)
      have hr := hmono.monotone (show u ≤ (1:Interval) from u.property.2)
      have he0 : g 0 = -1/2 := by rw [ht] at hl; linarith [hzero.1]
      have he1 : g 1 = 1/2 := by rw [hu] at hr; linarith [hone.2]
      rw [he0,he1]
    · have hl := hanti.antitone (show (0:Interval) ≤ u from u.property.1)
      have hr := hanti.antitone (show t ≤ (1:Interval) from t.property.2)
      have he0 : g 0 = 1/2 := by rw [hu] at hl; linarith [hzero.2]
      have he1 : g 1 = -1/2 := by rw [ht] at hr; linarith [hone.1]
      rw [he0,he1,Set.pair_comm]
  have hBranchSource (z : Metric.closedBall (0 : Plane) 1) :
      (pair z : S) ∈ M.cover.branch ↔ z = c 0 ∨ z = c 1 := by
    constructor
    · intro hz
      have hm : (pair z : S) ∈ (M.cover.branch : Set S) ∩ N.closedSet :=
        ⟨hz,(pair z).property⟩
      rw [N.marked_inside] at hm
      rcases hm with he | he
      · left
        apply pair.injective
        have hh : pair (c 0) = A 0 := pair.apply_symm_apply (A 0)
        exact (Subtype.ext he).trans hh.symm
      · right
        apply pair.injective
        have hh : pair (c 1) = A 1 := pair.apply_symm_apply (A 1)
        exact (Subtype.ext (Set.mem_singleton_iff.mp he)).trans hh.symm
    · rintro (rfl | rfl)
      · simpa only [c,Function.comp_apply,pair.apply_symm_apply,A,hzero] using a.val.start_marked
      · simpa only [c,Function.comp_apply,pair.apply_symm_apply,A,hone] using a.val.end_marked
  have hBranchCoordinate (z : Metric.closedBall (0 : Plane) 1) :
      (pair z : S) ∈ M.cover.branch ↔ z.val 1 = 0 ∧ |z.val 0| = (1/2 : ℝ) := by
    rw [hBranchSource]
    constructor
    · rintro (rfl | rfl)
      · refine ⟨(hcCore 0).2.1,?_⟩
        have he : g 0 ∈ ({(-1/2 : ℝ),1/2} : Set ℝ) :=
          hcoordinateEnds ▸ (by simp)
        rcases he with he | he
        · change |g 0| = 1/2
          rw [he]; norm_num
        · change |g 0| = 1/2
          rw [Set.mem_singleton_iff.mp he]; norm_num
      · refine ⟨(hcCore 1).2.1,?_⟩
        have he : g 1 ∈ ({(-1/2 : ℝ),1/2} : Set ℝ) :=
          hcoordinateEnds ▸ (by simp)
        rcases he with he | he
        · change |g 1| = 1/2
          rw [he]; norm_num
        · change |g 1| = 1/2
          rw [Set.mem_singleton_iff.mp he]; norm_num
    · rintro ⟨hz1,hz0⟩
      have hx : z.val 0 ∈ ({(-1/2 : ℝ),1/2} : Set ℝ) := by
        rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp hz0 with he | he
        · exact Or.inr (Set.mem_singleton_iff.mpr he)
        · exact Or.inl (by simpa only [neg_div] using he)
      rw [← hcoordinateEnds] at hx
      rcases hx with he | he
      · left
        apply Subtype.ext
        ext i
        fin_cases i
        · exact he
        · exact hz1.trans (hcCore 0).2.1.symm
      · right
        apply Subtype.ext
        ext i
        fin_cases i
        · exact Set.mem_singleton_iff.mp he
        · exact hz1.trans (hcCore 1).2.1.symm
  have hSquare : ∃ h : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
    h '' Metric.closedBall (0 : Schoenflies.Plane) 1 =
      {z | |z 0| ≤ 1 ∧ |z 1| ≤ 1} ∧
    (∀ z : Schoenflies.Plane, z 1 = 0 → h z = z) := by
    let K : Set Schoenflies.Plane := {z | |z 0| ≤ 1 ∧ |z 1| ≤ 1}
    have hKconv : Convex ℝ K := by
      intro x hx y hy a b ha hb hab
      constructor
      · change |a * x 0 + b * y 0| ≤ 1
        calc
          _ ≤ |a * x 0| + |b * y 0| := abs_add_le _ _
          _ = a * |x 0| + b * |y 0| := by
            rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
          _ ≤ 1 := by nlinarith [hx.1,hy.1]
      · change |a * x 1 + b * y 1| ≤ 1
        calc
          _ ≤ |a * x 1| + |b * y 1| := abs_add_le _ _
          _ = a * |x 1| + b * |y 1| := by
            rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
          _ ≤ 1 := by nlinarith [hx.2,hy.2]
    have hKclosed : IsClosed K := by
      dsimp [K]
      have hc0 : Continuous (fun z : Schoenflies.Plane => |z 0|) := by fun_prop
      have hc1 : Continuous (fun z : Schoenflies.Plane => |z 1|) := by fun_prop
      exact (isClosed_le hc0 continuous_const).inter (isClosed_le hc1 continuous_const)
    have hball : Metric.ball (0 : Schoenflies.Plane) 1 ⊆ K := by
      intro z hz
      have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
      exact ⟨(by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le z 0).trans hn.le),
        (by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le z 1).trans hn.le)⟩
    have hKnhds : K ∈ 𝓝 (0 : Schoenflies.Plane) :=
      Filter.mem_of_superset (Metric.ball_mem_nhds _ (by norm_num)) hball
    have hKbounded : Bornology.IsVonNBounded ℝ K := by
      have hsub : K ⊆ Metric.closedBall (0 : Schoenflies.Plane) 2 := by
        intro z hz
        have hsq : ‖z‖ ^ 2 ≤ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
          have h0 := abs_le.mp hz.1
          have h1 := abs_le.mp hz.2
          nlinarith
        have hn : ‖z‖ ≤ 2 := by nlinarith [norm_nonneg z]
        simpa only [Metric.mem_closedBall,dist_zero_right] using hn
      exact ((NormedSpace.isVonNBounded_of_isBounded ℝ Metric.isBounded_closedBall)).subset hsub
    have hDnhds : Metric.closedBall (0 : Schoenflies.Plane) 1 ∈ 𝓝 (0 : Schoenflies.Plane) :=
      Metric.closedBall_mem_nhds _ (by norm_num)
    let h := gaugeRescaleHomeomorph (Metric.closedBall (0 : Schoenflies.Plane) 1) K
      (convex_closedBall _ _) hDnhds (NormedSpace.isVonNBounded_of_isBounded ℝ Metric.isBounded_closedBall)
      hKconv hKnhds hKbounded
    have himage : h '' Metric.closedBall (0 : Schoenflies.Plane) 1 = K := by
      simpa only [Metric.isClosed_closedBall.closure_eq,hKclosed.closure_eq] using
        image_gaugeRescaleHomeomorph_closure (convex_closedBall _ _) hDnhds
          (NormedSpace.isVonNBounded_of_isBounded ℝ Metric.isBounded_closedBall) hKconv hKnhds hKbounded
    refine ⟨h,himage,?_⟩
    intro z hz
    have hnorm : ‖z‖ = |z 0| := by
      have hsq : ‖z‖ ^ 2 = (z 0)^2 := by
        rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,hz]
        ring
      nlinarith [norm_nonneg z,abs_nonneg (z 0),sq_abs (z 0)]
    have hGauge : gauge K z = gauge (Metric.closedBall (0 : Schoenflies.Plane) 1) z := by
      rw [gauge_def',gauge_def']
      congr 1
      ext r
      simp only [Set.mem_setOf_eq,Set.mem_sep_iff,Set.mem_Ioi]
      apply and_congr_right
      intro _
      change (|r⁻¹ * z 0| ≤ 1 ∧ |r⁻¹ * z 1| ≤ 1) ↔
        r⁻¹ • z ∈ Metric.closedBall (0 : Schoenflies.Plane) 1
      simp only [hz,mul_zero,abs_zero,zero_le_one,and_true,
        Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        hnorm,abs_mul]
    change gaugeRescale (Metric.closedBall (0 : Schoenflies.Plane) 1) K z = z
    by_cases hzero : z = 0
    · simp [hzero]
    · rw [gaugeRescale,hGauge,div_self,one_smul]
      rw [gauge_closedBall (by norm_num : (0 : ℝ) ≤ 1),div_one]
      exact norm_ne_zero_iff.mpr hzero
  obtain ⟨h,himage,haxis⟩ := hSquare
  let K : Set Plane := {z | |z 0| ≤ 1 ∧ |z 1| ≤ 1}
  let R : Set (ℝ × ℝ) := Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  let e : (ℝ × ℝ) ≃L[ℝ] Plane :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  have he0 (z : ℝ × ℝ) : (e z) 0 = z.1 := rfl
  have he1 (z : ℝ × ℝ) : (e z) 1 = z.2 := rfl
  have heR : e '' R = K := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨abs_le.mpr hx.1,abs_le.mpr hx.2⟩
    · intro hz
      refine ⟨(z 0,z 1),⟨abs_le.mp hz.1,abs_le.mp hz.2⟩,?_⟩
      ext i
      fin_cases i <;> rfl
  let u : Metric.closedBall (0 : Plane) 1 ≃ₜ K :=
    (h.image (Metric.closedBall (0 : Plane) 1)).trans (Homeomorph.setCongr himage)
  let v : R ≃ₜ K := (e.toHomeomorph.image R).trans (Homeomorph.setCongr heR)
  let j : R ≃ₜ N.closedSet := v.trans (u.symm.trans pair)
  have huval (z : Metric.closedBall (0 : Plane) 1) : (u z : Plane) = h z := rfl
  have hvval (z : R) : (v z : Plane) = e z.val := rfl
  have hux (z : R) : h (u.symm (v z)).val = e z.val := by
    rw [← huval,u.apply_symm_apply,hvval]
  have haxisBack (z : R) (hz : z.val.2 = 0) :
      (u.symm (v z)).val = e z.val := by
    have hf : h (e z.val) = e z.val := haxis _ (by rw [he1,hz])
    exact h.injective ((hux z).trans hf.symm)
  have hjCore : (fun z : R => (j z : S)) ''
      {z : R | z.val.2 = 0 ∧ |z.val.1| ≤ (1/2 : ℝ)} = a.image := by
    rw [← hcore]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨u.symm (v z),?_,rfl⟩
      change (u.symm (v z)).val ∈ ClassificationSchoenflies.centralHalfDiameter
      refine ⟨(u.symm (v z)).property,?_,?_⟩
      · rw [haxisBack z hz.1,he1,hz.1]
      · rw [haxisBack z hz.1,he0]
        exact hz.2
    · rintro ⟨z,hz,rfl⟩
      let x : R := ⟨(z.val 0,z.val 1),⟨by
        have hx := abs_le.mp hz.2.2
        constructor <;> linarith,by rw [hz.2.1]; norm_num⟩⟩
      have he : e x.val = z.val := by ext i; fin_cases i <;> rfl
      have huv : u z = v x := by
        apply Subtype.ext
        rw [huval,hvval,he,haxis _ hz.2.1]
      refine ⟨x,⟨hz.2.1,hz.2.2⟩,?_⟩
      change (pair (u.symm (v x)) : S) = (pair z : S)
      rw [← huv,u.symm_apply_apply]
  have hjBranch (z : R) : (j z : S) ∈ M.cover.branch ↔
      z.val.2 = 0 ∧ |z.val.1| = (1/2 : ℝ) := by
    change (pair (u.symm (v z)) : S) ∈ M.cover.branch ↔ _
    rw [hBranchCoordinate]
    constructor
    · rintro ⟨hz0,hz1⟩
      have hf : h (u.symm (v z)).val = (u.symm (v z)).val := haxis _ hz0
      have he : e z.val = (u.symm (v z)).val := (hux z).symm.trans hf
      exact ⟨by rw [← he,he1] at hz0; exact hz0,
        by rw [← he,he0] at hz1; exact hz1⟩
    · rintro ⟨hz0,hz1⟩
      rw [haxisBack z hz0,he1,he0]
      exact ⟨hz0,hz1⟩
  let f : C(R,S) := ⟨fun z => (j z : S),continuous_subtype_val.comp j.continuous⟩
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp j.isEmbedding
  have hfrange : Set.range f = N.closedSet := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact (j z).property
    · intro hx
      exact ⟨j.symm ⟨x,hx⟩,congrArg Subtype.val (j.apply_symm_apply ⟨x,hx⟩)⟩
  let p : R := ⟨(-1/2,0),by norm_num [R]⟩
  let q : R := ⟨(1/2,0),by norm_num [R]⟩
  have hmarks (z : R) : f z ∈ M.cover.branch ↔ z=p ∨ z=q := by
    change (j z : S) ∈ M.cover.branch ↔ z=p ∨ z=q
    rw [hjBranch]
    constructor
    · rintro ⟨hz,ha⟩
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1/2)).mp ha with ha | ha
      · right
        apply Subtype.ext
        exact Prod.ext ha hz
      · left
        apply Subtype.ext
        exact Prod.ext (by simpa only [p,neg_div] using ha) hz
    · rintro (rfl | rfl) <;> norm_num [p,q]
  have hp : p.val ∈ interior R := by
    change p.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)
    rw [interior_prod_eq,interior_Icc]
    change (-1 < (-1/2:ℝ) ∧ (-1/2:ℝ) < 1) ∧ (-1 < (0:ℝ) ∧ (0:ℝ) < 1)
    norm_num
  have hq : q.val ∈ interior R := by
    change q.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)
    rw [interior_prod_eq,interior_Icc]
    change (-1 < (1/2:ℝ) ∧ (1/2:ℝ) < 1) ∧ (-1 < (0:ℝ) ∧ (0:ℝ) < 1)
    norm_num
  let k : ℝ := 0
  have hk0 : -1 < k := by norm_num [k]
  have hk1 : k < 1 := by norm_num [k]
  have hpk : p.val.1 < k := by norm_num [p,k]
  have hkq : k < q.val.1 := by norm_num [q,k]
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  let : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by simp⟩
  let : LocallyPathConnectedSpace Interval := (convex_Icc (0:ℝ) 1).locallyPathConnectedSpace
  let L := Icc (-1:ℝ) k ×ˢ Icc (-1:ℝ) 1
  let R := Icc k (1:ℝ) ×ˢ Icc (-1:ℝ) 1
  let K := Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  have hsubL : L ⊆ K := by
    rintro z ⟨hx,hy⟩; exact ⟨⟨hx.1,hx.2.trans hk1.le⟩,hy⟩
  have hsubR : R ⊆ K := by
    rintro z ⟨hx,hy⟩; exact ⟨⟨hk0.le.trans hx.1,hx.2⟩,hy⟩
  let f₀ : C(L,S) := f.comp ⟨Set.inclusion hsubL,continuous_inclusion hsubL⟩
  let f₁ : C(R,S) := f.comp ⟨Set.inclusion hsubR,continuous_inclusion hsubR⟩
  have hpb : (-1<p.val.1 ∧ p.val.1<1) ∧ (-1<p.val.2 ∧ p.val.2<1) := by
    norm_num [p]
  have hqb : (-1<q.val.1 ∧ q.val.1<1) ∧ (-1<q.val.2 ∧ q.val.2<1) := by
    norm_num [q]
  let m₀ : L := ⟨p.val,⟨⟨hpb.1.1.le,hpk.le⟩,⟨hpb.2.1.le,hpb.2.2.le⟩⟩⟩
  let m₁ : R := ⟨q.val,⟨⟨hkq.le,hqb.1.2.le⟩,⟨hqb.2.1.le,hqb.2.2.le⟩⟩⟩
  have hm₀ : m₀.val ∈ interior L := by
    simp only [L,interior_prod_eq,interior_Icc,mem_prod,mem_Ioo]
    exact ⟨⟨hpb.1.1,hpk⟩,hpb.2⟩
  have hm₁ : m₁.val ∈ interior R := by
    simp only [R,interior_prod_eq,interior_Icc,mem_prod,mem_Ioo]
    exact ⟨⟨hkq,hqb.1.2⟩,hqb.2⟩
  have hc₀ (z : L) : f₀ z ∈ M.cover.branch ↔ z=m₀ := by
    change f ⟨z.val,hsubL z.property⟩ ∈ M.cover.branch ↔ z=m₀
    rw [hmarks]
    constructor
    · rintro (he | he)
      · apply Subtype.ext; exact congrArg (fun z : K => z.val) he
      · have hx := congrArg (fun z : K => z.val.1) he
        exact False.elim ((not_le_of_gt hkq) (hx ▸ z.property.1.2))
    · intro he; left
      apply Subtype.ext; exact congrArg (fun z : L => z.val) he
  have hc₁ (z : R) : f₁ z ∈ M.cover.branch ↔ z=m₁ := by
    change f ⟨z.val,hsubR z.property⟩ ∈ M.cover.branch ↔ z=m₁
    rw [hmarks]
    constructor
    · rintro (he | he)
      · have hx := congrArg (fun z : K => z.val.1) he
        exact False.elim ((not_le_of_gt hpk) (hx ▸ z.property.1.1))
      · apply Subtype.ext; exact congrArg (fun z : K => z.val) he
    · intro he; right
      apply Subtype.ext; exact congrArg (fun z : R => z.val) he
  let θ : C(Interval,K) := ⟨fun t => ⟨(k,2*t.val-1),⟨⟨hk0.le,hk1.le⟩,
    ⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩⟩,by
      apply Continuous.subtype_mk
      exact continuous_const.prodMk ((continuous_subtype_val.const_mul 2).sub continuous_const)⟩
  let g : C(Interval,S) := f.comp θ
  have hθinj : Function.Injective θ := by
    intro s t he
    have h := congrArg (fun z : K => z.val.2) he
    apply Subtype.ext
    dsimp [θ] at h
    linarith
  have hg : IsEmbedding g := hf.comp (θ.continuous.isClosedEmbedding hθinj).isEmbedding
  have havoid (t) : g t ∉ M.cover.branch := by
    change f (θ t) ∉ M.cover.branch
    rw [hmarks]
    rintro (he | he)
    · have hx := congrArg (fun z : K => z.val.1) he
      change k=p.val.1 at hx
      linarith
    · have hx := congrArg (fun z : K => z.val.1) he
      change k=q.val.1 at hx
      linarith
  obtain ⟨η,δ,hη,hδ,hηπ,hδπ,hδdeck,hdisj,hcover⟩ :=
    M.cover.compact_simplyConnected_two_sheet_lifts g hg havoid 0
  obtain ⟨β₀,β₁,he₀,he₁,hcoll₀,hcoll₁,hr₀,hr₁,hhalf₀,hhalf₁,houterloops⟩ :=
    rectangle_cut_boundary_loops_exterior (-1) k 1 (-1) 1 hk0 hk1 (by norm_num)
  have hseg (t : Interval) : Path.segment (k,(-1:ℝ)) (k,1) t=(k,2*t.val-1) := by
    simp [Path.segment_apply,AffineMap.lineMap_apply,smul_eq_mul]
    ring
  have hp₀ (t) : M.cover.projection (η t)=f₀ (β₀ (halfInterval t)) := by
    rw [hηπ]
    change f (θ t)=f ⟨(β₀ (halfInterval t)).val,hsubL (β₀ (halfInterval t)).property⟩
    apply congrArg f
    apply Subtype.ext
    rw [hhalf₀,hseg]
    rfl
  have hp₁ (t) : M.cover.projection (η t)=f₁ (β₁ (halfInterval t)) := by
    rw [hηπ]
    change f (θ t)=f ⟨(β₁ (halfInterval t)).val,hsubR (β₁ (halfInterval t)).property⟩
    apply congrArg f
    apply Subtype.ext
    rw [hhalf₁,hseg]
    rfl
  have hbaseInter : Set.range f₀ ∩ Set.range f₁=Set.range g := by
    ext y
    constructor
    · rintro ⟨⟨x,hx⟩,⟨z,hz⟩⟩
      have hev : x.val=z.val := congrArg (fun z : K => z.val) (hf.injective (hx.trans hz.symm))
      have hxk : x.val.1=k := by
        have he1 := congrArg Prod.fst hev
        linarith [x.property.1.2,z.property.1.1]
      let t : Interval := ⟨(x.val.2+1)/2,⟨by linarith [x.property.2.1],by linarith [x.property.2.2]⟩⟩
      refine ⟨t,?_⟩
      change f (θ t)=y
      trans f₀ x
      · apply congrArg f
        apply Subtype.ext
        apply Prod.ext
        · exact hxk.symm
        · dsimp [θ,t]; ring
      · exact hx
    · rintro ⟨t,rfl⟩
      have hl : (θ t).val ∈ L := ⟨⟨hk0.le,le_rfl⟩,(θ t).property.2⟩
      have hr : (θ t).val ∈ R := ⟨⟨le_rfl,hk1.le⟩,(θ t).property.2⟩
      exact ⟨⟨⟨(θ t).val,hl⟩,rfl⟩,⟨⟨(θ t).val,hr⟩,rfl⟩⟩
  have hbaseUnion : Set.range f₀ ∪ Set.range f₁=Set.range f := by
    ext y
    constructor
    · rintro (⟨x,rfl⟩ | ⟨x,rfl⟩)
      · exact ⟨⟨x.val,hsubL x.property⟩,rfl⟩
      · exact ⟨⟨x.val,hsubR x.property⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      rcases le_total x.val.1 k with h | h
      · exact Or.inl ⟨⟨x.val,⟨⟨x.property.1.1,h⟩,x.property.2⟩⟩,rfl⟩
      · exact Or.inr ⟨⟨x.val,⟨⟨h,x.property.1.2⟩,x.property.2⟩⟩,rfl⟩
  have hinter : (M.cover.projection ⁻¹' Set.range f₀) ∩
      (M.cover.projection ⁻¹' Set.range f₁)=Set.range η ∪ Set.range δ := by
    rw [← Set.preimage_inter,hbaseInter,← hcover]
  let ρ₀ : C(Interval,L) := ⟨fun r => ⟨((r.val-1)/2,0),by
    dsimp [L,k]
    exact ⟨⟨by linarith [r.property.1],by linarith [r.property.2]⟩,by norm_num⟩⟩,
    by fun_prop⟩
  let ρ₁ : C(Interval,R) := ⟨fun r => ⟨((1-r.val)/2,0),by
    dsimp [R,k]
    exact ⟨⟨by linarith [r.property.2],by linarith [r.property.1]⟩,by norm_num⟩⟩,
    by fun_prop⟩
  have hCoreCut : Set.range (f₀ ∘ ρ₀) ∪ Set.range (f₁ ∘ ρ₁) = a.image := by
    rw [← hjCore]
    ext y
    constructor
    · rintro (⟨r,rfl⟩ | ⟨r,rfl⟩)
      · refine ⟨⟨(ρ₀ r).val,hsubL (ρ₀ r).property⟩,?_,rfl⟩
        change (0:ℝ)=0 ∧ |(r.val-1)/2| ≤ 1/2
        refine ⟨rfl,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith [r.property.1,r.property.2]
      · refine ⟨⟨(ρ₁ r).val,hsubR (ρ₁ r).property⟩,?_,rfl⟩
        change (0:ℝ)=0 ∧ |(1-r.val)/2| ≤ 1/2
        refine ⟨rfl,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith [r.property.1,r.property.2]
    · rintro ⟨z,⟨hz0,hz1⟩,rfl⟩
      have hb := abs_le.mp hz1
      by_cases hz : z.val.1 ≤ 0
      · left
        let r : Interval := ⟨2*z.val.1+1,⟨by linarith [hb.1],by linarith⟩⟩
        refine ⟨r,?_⟩
        change f ⟨(ρ₀ r).val,hsubL (ρ₀ r).property⟩ = (j z : S)
        apply congrArg f
        apply Subtype.ext
        apply Prod.ext
        · dsimp [ρ₀,r]; ring
        · exact hz0.symm
      · right
        let r : Interval := ⟨1-2*z.val.1,⟨by linarith [hb.2],by linarith⟩⟩
        refine ⟨r,?_⟩
        change f ⟨(ρ₁ r).val,hsubR (ρ₁ r).property⟩ = (j z : S)
        apply congrArg f
        apply Subtype.ext
        apply Prod.ext
        · dsimp [ρ₁,r]; ring
        · exact hz0.symm
  have hLiftedCoreCut :
      M.cover.projection ⁻¹' Set.range (f₀ ∘ ρ₀) ∪
      M.cover.projection ⁻¹' Set.range (f₁ ∘ ρ₁) =
      M.cover.projection ⁻¹' a.image := by
    rw [← Set.preimage_union,hCoreCut]
  let W : Metric.closedBall (0 : Plane) 1 ≃ₜ K := u.trans v.symm
  let α₀ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    ((Homeomorph.mulLeft₀ (1/2 : ℝ) (by norm_num)).trans
      (Homeomorph.addRight (-1/2 : ℝ))).prodCongr (Homeomorph.refl ℝ)
  let α₁ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    ((Homeomorph.mulLeft₀ (1/2 : ℝ) (by norm_num)).trans
      (Homeomorph.addRight (1/2 : ℝ))).prodCongr (Homeomorph.refl ℝ)
  have hα₀ (z : ℝ × ℝ) : α₀ z = ((z.1-1)/2,z.2) := by
    apply Prod.ext
    · change (1/2:ℝ)*z.1 + -1/2 = (z.1-1)/2
      ring
    · rfl
  have hα₁ (z : ℝ × ℝ) : α₁ z = ((z.1+1)/2,z.2) := by
    apply Prod.ext
    · change (1/2:ℝ)*z.1 + 1/2 = (z.1+1)/2
      ring
    · rfl
  have hα₀Image : α₀ '' K = L := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hα₀]
      change (-1 ≤ (x.1-1)/2 ∧ (x.1-1)/2 ≤ k) ∧ x.2 ∈ Icc (-1:ℝ) 1
      refine ⟨⟨?_,?_⟩,hx.2⟩ <;> (try dsimp [k]) <;> linarith [hx.1.1,hx.1.2]
    · intro hz
      refine ⟨(2*z.1+1,z.2),⟨⟨?_,?_⟩,hz.2⟩,?_⟩
      · linarith [hz.1.1]
      · dsimp [L,k] at hz
        linarith [hz.1.2]
      · rw [hα₀]
        apply Prod.ext
        · dsimp; ring
        · rfl
  have hα₁Image : α₁ '' K = R := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hα₁]
      change (k ≤ (x.1+1)/2 ∧ (x.1+1)/2 ≤ 1) ∧ x.2 ∈ Icc (-1:ℝ) 1
      refine ⟨⟨?_,?_⟩,hx.2⟩ <;> (try dsimp [k]) <;> linarith [hx.1.1,hx.1.2]
    · intro hz
      refine ⟨(2*z.1-1,z.2),⟨⟨?_,?_⟩,hz.2⟩,?_⟩
      · dsimp [R,k] at hz
        linarith [hz.1.1]
      · linarith [hz.1.2]
      · rw [hα₁]
        apply Prod.ext
        · dsimp; ring
        · rfl
  let B₀ : Metric.closedBall (0 : Plane) 1 ≃ₜ L :=
    W.trans ((α₀.image K).trans (Homeomorph.setCongr hα₀Image))
  let B₁ : Metric.closedBall (0 : Plane) 1 ≃ₜ R :=
    W.trans ((α₁.image K).trans (Homeomorph.setCongr hα₁Image))
  have hWVal (z : Metric.closedBall (0 : Plane) 1) :
      e (W z).val = h z.val := by
    have he := congrArg Subtype.val (v.apply_symm_apply (u z))
    exact he.trans (huval z)
  have hWaxis (z : Metric.closedBall (0 : Plane) 1) (hz : z.val 1 = 0) :
      (W z).val = (z.val 0,0) := by
    apply Prod.ext
    · have he := congrArg (fun w : Plane => w 0) ((hWVal z).trans (haxis _ hz))
      rw [he0] at he
      exact he
    · have he := congrArg (fun w : Plane => w 1) ((hWVal z).trans (haxis _ hz))
      rw [he1] at he
      exact he.trans hz
  have hB₀Val (z : Metric.closedBall (0 : Plane) 1) :
      (B₀ z).val = α₀ (W z).val := rfl
  have hB₁Val (z : Metric.closedBall (0 : Plane) 1) :
      (B₁ z).val = α₁ (W z).val := rfl
  let origin : Metric.closedBall (0 : Plane) 1 := ⟨0,by simp⟩
  have hB₀origin : B₀ origin = m₀ := by
    apply Subtype.ext
    rw [hB₀Val,hWaxis _ (by simp [origin]),hα₀]
    change ((0-1)/2,(0:ℝ)) = (-1/2,0)
    norm_num
  have hB₁origin : B₁ origin = m₁ := by
    apply Subtype.ext
    rw [hB₁Val,hWaxis _ (by simp [origin]),hα₁]
    change ((0+1)/2,(0:ℝ)) = (1/2,0)
    norm_num
  let d₀ : C(Metric.closedBall (0 : Plane) 1,S) := f₀.comp ⟨B₀,B₀.continuous⟩
  let d₁ : C(Metric.closedBall (0 : Plane) 1,S) := f₁.comp ⟨B₁,B₁.continuous⟩
  have hd₀ : IsEmbedding d₀ :=
    (hf.comp (Topology.IsEmbedding.inclusion hsubL)).comp B₀.isEmbedding
  have hd₁ : IsEmbedding d₁ :=
    (hf.comp (Topology.IsEmbedding.inclusion hsubR)).comp B₁.isEmbedding
  have hd₀Mark (z : Metric.closedBall (0 : Plane) 1) :
      d₀ z ∈ M.cover.branch ↔ z = origin := by
    change f₀ (B₀ z) ∈ M.cover.branch ↔ z=origin
    rw [hc₀,← hB₀origin,B₀.injective.eq_iff]
  have hd₁Mark (z : Metric.closedBall (0 : Plane) 1) :
      d₁ z ∈ M.cover.branch ↔ z = origin := by
    change f₁ (B₁ z) ∈ M.cover.branch ↔ z=origin
    rw [hc₁,← hB₁origin,B₁.injective.eq_iff]
  let G₀ : Plane ≃ₜ (ℝ × ℝ) := (h.trans e.toHomeomorph.symm).trans α₀
  let G₁ : Plane ≃ₜ (ℝ × ℝ) := (h.trans e.toHomeomorph.symm).trans α₁
  have hB₀Global (z : Metric.closedBall (0 : Plane) 1) : (B₀ z).val = G₀ z.val := by
    rw [hB₀Val]
    apply congrArg α₀
    apply e.injective
    change e (W z).val = e (e.symm (h z.val))
    rw [e.apply_symm_apply]
    exact hWVal z
  have hB₁Global (z : Metric.closedBall (0 : Plane) 1) : (B₁ z).val = G₁ z.val := by
    rw [hB₁Val]
    apply congrArg α₁
    apply e.injective
    change e (W z).val = e (e.symm (h z.val))
    rw [e.apply_symm_apply]
    exact hWVal z
  have hGlobalImage {T : Set (ℝ × ℝ)}
      (B : Metric.closedBall (0 : Plane) 1 ≃ₜ T)
      (G : Plane ≃ₜ (ℝ × ℝ))
      (hb : ∀ z : Metric.closedBall (0 : Plane) 1, (B z).val = G z.val) :
      G '' Metric.closedBall (0 : Plane) 1 = T := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      rw [← hb ⟨z,hz⟩]
      exact (B ⟨z,hz⟩).property
    · intro hy
      let z := B.symm ⟨y,hy⟩
      refine ⟨z.val,z.property,?_⟩
      rw [← hb z]
      exact congrArg Subtype.val (B.apply_symm_apply ⟨y,hy⟩)
  have hBoundaryNorm {T : Set (ℝ × ℝ)}
      (B : Metric.closedBall (0 : Plane) 1 ≃ₜ T)
      (G : Plane ≃ₜ (ℝ × ℝ))
      (hb : ∀ z : Metric.closedBall (0 : Plane) 1, (B z).val = G z.val)
      (z : Metric.closedBall (0 : Plane) 1) :
      (B z).val ∈ frontier T ↔ ‖z.val‖ = 1 := by
    have him := hGlobalImage B G hb
    have hfront : G '' frontier (Metric.closedBall (0 : Plane) 1) = frontier T := by
      rw [G.image_frontier,him]
    rw [hb,← hfront,frontier_closedBall (0 : Plane) (by norm_num : (1:ℝ) ≠ 0)]
    constructor
    · rintro ⟨x,hx,he⟩
      have hxz := G.injective he
      subst x
      simpa only [Metric.mem_sphere,dist_zero_right] using hx
    · intro hz
      exact ⟨z.val,by simpa only [Metric.mem_sphere,dist_zero_right] using hz,rfl⟩
  let βd₀ : C(Interval,Metric.closedBall (0 : Plane) 1) :=
    ⟨B₀.symm ∘ β₀,B₀.symm.continuous.comp β₀.continuous⟩
  let βd₁ : C(Interval,Metric.closedBall (0 : Plane) 1) :=
    ⟨B₁.symm ∘ β₁,B₁.symm.continuous.comp β₁.continuous⟩
  have hβd₀Ends : βd₀ 0 = βd₀ 1 := congrArg B₀.symm he₀
  have hβd₁Ends : βd₁ 0 = βd₁ 1 := congrArg B₁.symm he₁
  have hβd₀Coll (s t : Interval) (he : βd₀ s = βd₀ t) :
      s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) :=
    hcoll₀ s t (B₀.symm.injective he)
  have hβd₁Coll (s t : Interval) (he : βd₁ s = βd₁ t) :
      s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) :=
    hcoll₁ s t (B₁.symm.injective he)
  have hβd₀Range : Set.range βd₀ = {z | ‖z.val‖ = 1} := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      apply (hBoundaryNorm B₀ G₀ hB₀Global (βd₀ t)).mp
      change (B₀ (B₀.symm (β₀ t))).val ∈ frontier L
      rw [B₀.apply_symm_apply]
      have hb := Set.mem_range_self t (f:=β₀)
      rw [hr₀] at hb
      exact hb
    · intro hz
      have hb := (hBoundaryNorm B₀ G₀ hB₀Global z).mpr hz
      obtain ⟨t,ht⟩ : B₀ z ∈ Set.range β₀ := by rw [hr₀]; exact hb
      exact ⟨t,by change B₀.symm (β₀ t) = z; rw [ht,B₀.symm_apply_apply]⟩
  have hβd₁Range : Set.range βd₁ = {z | ‖z.val‖ = 1} := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      apply (hBoundaryNorm B₁ G₁ hB₁Global (βd₁ t)).mp
      change (B₁ (B₁.symm (β₁ t))).val ∈ frontier R
      rw [B₁.apply_symm_apply]
      have hb := Set.mem_range_self t (f:=β₁)
      rw [hr₁] at hb
      exact hb
    · intro hz
      have hb := (hBoundaryNorm B₁ G₁ hB₁Global z).mpr hz
      obtain ⟨t,ht⟩ : B₁ z ∈ Set.range β₁ := by rw [hr₁]; exact hb
      exact ⟨t,by change B₁.symm (β₁ t) = z; rw [ht,B₁.symm_apply_apply]⟩
  have hd₀η (t : Interval) : M.cover.projection (η t) = d₀ (βd₀ (halfInterval t)) := by
    rw [hp₀]
    change f₀ (β₀ (halfInterval t)) = f₀ (B₀ (B₀.symm (β₀ (halfInterval t))))
    rw [B₀.apply_symm_apply]
  have hd₁η (t : Interval) : M.cover.projection (η t) = d₁ (βd₁ (halfInterval t)) := by
    rw [hp₁]
    change f₁ (β₁ (halfInterval t)) = f₁ (B₁ (B₁.symm (β₁ (halfInterval t))))
    rw [B₁.apply_symm_apply]
  let eastVec : Plane := WithLp.toLp 2 ![(1:ℝ),0]
  let westVec : Plane := WithLp.toLp 2 ![(-1:ℝ),0]
  have heastNorm : ‖eastVec‖ = 1 := by
    have hsq : ‖eastVec‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [eastVec,Fin.sum_univ_two]
    nlinarith [norm_nonneg eastVec]
  have hwestNorm : ‖westVec‖ = 1 := by
    have hsq : ‖westVec‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [westVec,Fin.sum_univ_two]
    nlinarith [norm_nonneg westVec]
  let east : Metric.closedBall (0 : Plane) 1 := ⟨eastVec,by
    simpa only [Metric.mem_closedBall,dist_zero_right,heastNorm] using (le_refl (1:ℝ))⟩
  let west : Metric.closedBall (0 : Plane) 1 := ⟨westVec,by
    simpa only [Metric.mem_closedBall,dist_zero_right,hwestNorm] using (le_refl (1:ℝ))⟩
  let angle : Interval := ⟨1/4,by norm_num⟩
  let mid : Interval := ⟨1/2,by norm_num⟩
  have hhalfAngle : halfInterval mid = angle := by
    apply Subtype.ext
    norm_num [halfInterval,mid,angle]
  have hβd₀Angle : βd₀ angle = east := by
    apply B₀.injective
    change B₀ (B₀.symm (β₀ angle)) = B₀ east
    rw [B₀.apply_symm_apply]
    apply Subtype.ext
    rw [hB₀Val,hWaxis _ (by simp [east,eastVec]),hα₀]
    rw [← hhalfAngle,hhalf₀,hseg]
    norm_num [east,eastVec,k,mid]
  have hβd₁Angle : βd₁ angle = west := by
    apply B₁.injective
    change B₁ (B₁.symm (β₁ angle)) = B₁ west
    rw [B₁.apply_symm_apply]
    apply Subtype.ext
    rw [hB₁Val,hWaxis _ (by simp [west,westVec]),hα₁]
    rw [← hhalfAngle,hhalf₁,hseg]
    norm_num [west,westVec,k,mid]
  have hρ₀Literal (r : Interval) :
      d₀ (discRadialContraction origin r (βd₀ angle)) = f₀ (ρ₀ r) := by
    rw [hβd₀Angle]
    change f₀ (B₀ (discRadialContraction origin r east)) = f₀ (ρ₀ r)
    apply congrArg f₀
    apply Subtype.ext
    rw [hB₀Val,hWaxis _ (by simp [discRadialContraction,origin,east,eastVec]),hα₀]
    apply Prod.ext
    · dsimp [discRadialContraction,origin,east,eastVec,ρ₀]
      ring
    · simp [discRadialContraction,origin,east,eastVec,ρ₀]
  have hρ₁Literal (r : Interval) :
      d₁ (discRadialContraction origin r (βd₁ angle)) = f₁ (ρ₁ r) := by
    rw [hβd₁Angle]
    change f₁ (B₁ (discRadialContraction origin r west)) = f₁ (ρ₁ r)
    apply congrArg f₁
    apply Subtype.ext
    rw [hB₁Val,hWaxis _ (by simp [discRadialContraction,origin,west,westVec]),hα₁]
    apply Prod.ext
    · dsimp [discRadialContraction,origin,west,westVec,ρ₁]
      ring
    · simp [discRadialContraction,origin,west,westVec,ρ₁]
  have hPolar : ∀
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hends : β 0 = β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β = {z | ‖z.val‖=1})
    (e : E) (he : M.cover.projection e = f (β 0)),
    ∃ H : OneMarkPolarCell ≃ₜ M.cover.projection ⁻¹' Set.range f,
      (H (Quot.mk oneMarkPolarRel ((1,0),false))).val=e ∧
      (∀ x : OneMarkPolarStrip,
        M.cover.projection (H (Quot.mk oneMarkPolarRel x)).val =
          f (discRadialContraction m x.1.1 (β x.1.2))) ∧
      (∀ t : Interval,
        Set.range (fun r : Interval => (H (Quot.mk oneMarkPolarRel ((r,t),false))).val) ∪
        Set.range (fun r : Interval => (H (Quot.mk oneMarkPolarRel ((r,t),true))).val) =
          M.cover.projection ⁻¹' Set.range (fun r : Interval =>
            f (discRadialContraction m r (β t)))) ∧
      ∃ γ : C(Interval,E),
        (∀ t : Interval, (H (Quot.mk oneMarkPolarRel ((1,t),false))).val = γ t) ∧
        (∀ r t : Interval,
          (H (Quot.mk oneMarkPolarRel ((r,t),true))).val =
            M.cover.deck (H (Quot.mk oneMarkPolarRel ((r,t),false))).val) ∧
        (∀ t : Interval, M.cover.projection (γ t) = f (β t)) ∧ γ 0 = e := by
    intro f hf m hm honly β hends hcoll hrange e he
    let : ClosedSurface E := Classical.choice M.genusTwo.2.1
    have hFull :
      ∃ h : Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ
          Metric.closedBall (0:Schoenflies.Plane) 1,
      ∃ L : C(Interval × Interval,E),
        (∀ z, (h z).val = z.val + (1-‖z.val‖) • m.val) ∧
        h ⟨0,by simp⟩=m ∧ (∀ z, ‖z.val‖=1 → h z=z) ∧ L (1,0)=e ∧
        (∀ r t : Interval, M.cover.projection (L (r,t)) =
          f (discRadialContraction m r (β t))) ∧
        (∀ r : Interval, L (r,1)=M.cover.deck (L (r,0))) ∧
        (∀ t t' : Interval, L (0,t)=L (0,t')) ∧
        Set.range L ∪ M.cover.deck '' Set.range L =
          M.cover.projection ⁻¹' Set.range f := by
        obtain ⟨h,hexpl,hzero,hboundary⟩ := CurveComplex.closed_disc_recenter m hm
        let f' : C(Metric.closedBall (0:Schoenflies.Plane) 1,S) := f.comp ⟨h,h.continuous⟩
        let z₀ : Metric.closedBall (0:Schoenflies.Plane) 1 := ⟨0,by simp⟩
        have honly' (z) : f' z ∈ M.cover.branch ↔ z=z₀ := by
          change f (h z) ∈ M.cover.branch ↔ z=z₀
          rw [honly]
          exact ⟨fun hz => h.injective (hz.trans hzero.symm),fun hz => hz ▸ hzero⟩
        have hnorm (t : Interval) : ‖(β t).val‖=1 := by
          have hh := Set.mem_range_self t (f := β)
          rw [hrange] at hh
          exact hh
        have he' : M.cover.projection e = f' (β 0) := by
          change M.cover.projection e=f (h (β 0))
          rw [hboundary _ (hnorm 0)]
          exact he
        obtain ⟨Γ,hΓanchor,hΓπ,hΓedge,hΓzero⟩ :=
          M.one_mark_disc_anchored_radial_filling f' (hf.comp h.isEmbedding) z₀
            (by simp [z₀]) honly' β hends hcoll hrange e he'
        let L : C(Interval × Interval,E) :=
          Γ.comp ⟨fun z => ⟨(z.1.val,z.2.val),⟨z.1.property,z.2.property⟩⟩,
            ((continuous_subtype_val.comp continuous_fst).prodMk
              (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
        have hπ (r t : Interval) : M.cover.projection (L (r,t)) =
            f (h (discRadialContraction z₀ r (β t))) := hΓπ r t
        have hπval (r t : Interval) :
            (discRadialContraction z₀ r (β t)).val = (r:ℝ) • (β t).val := by
          simp [discRadialContraction,z₀]
        refine ⟨h,L,hexpl,hzero,hboundary,hΓanchor,?_,hΓedge,hΓzero,?_⟩
        · intro r t
          rw [hπ]
          apply congrArg f
          apply Subtype.ext
          rw [hexpl, hπval]
          change (r:ℝ) • (β t).val + (1-‖(r:ℝ) • (β t).val‖) • m.val =
            (1-(r:ℝ)) • m.val + (r:ℝ) • (β t).val
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg r.property.1,
            hnorm, mul_one]
          exact add_comm _ _
        · ext y
          constructor
          · rintro (⟨⟨r,t⟩,rfl⟩ | ⟨x,⟨⟨r,t⟩,rfl⟩,rfl⟩)
            · exact ⟨h (discRadialContraction z₀ r (β t)),(hπ r t).symm⟩
            · exact ⟨h (discRadialContraction z₀ r (β t)),
                ((M.cover.projection_deck (L (r,t))).trans (hπ r t)).symm⟩
          · rintro ⟨z,hz⟩
            let z' := h.symm z
            have hz'norm : ‖z'.val‖ ≤ 1 := by
              simpa only [Metric.mem_closedBall,dist_zero_right] using z'.property
            let r : Interval := ⟨‖z'.val‖,⟨norm_nonneg _,hz'norm⟩⟩
            have hrad : ∃ t : Interval, discRadialContraction z₀ r (β t)=z' := by
              by_cases hz' : z'.val=0
              · refine ⟨0,?_⟩
                apply Subtype.ext
                simp [discRadialContraction,z₀,r,hz']
              · have hpos : 0 < ‖z'.val‖ := norm_pos_iff.mpr hz'
                let u : Metric.closedBall (0:Schoenflies.Plane) 1 :=
                  ⟨‖z'.val‖⁻¹ • z'.val,by
                    simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,
                      Real.norm_eq_abs,abs_inv,abs_of_pos hpos,inv_mul_cancel₀ (ne_of_gt hpos),le_refl]⟩
                have hu : ‖u.val‖=1 := by
                  simp [u,norm_smul,ne_of_gt hpos]
                have hurange : u ∈ Set.range β := by
                  rw [hrange]
                  exact hu
                obtain ⟨t,ht⟩ := hurange
                refine ⟨t,?_⟩
                apply Subtype.ext
                rw [hπval,ht]
                change ‖z'.val‖ • (‖z'.val‖⁻¹ • z'.val)=z'.val
                rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hpos),one_smul]
            obtain ⟨t,ht⟩ := hrad
            have hproj : M.cover.projection (L (r,t))=M.cover.projection y := by
              rw [hπ,ht]
              exact (congrArg f (h.apply_symm_apply z)).trans hz
            rcases (M.cover.fiber_pair (L (r,t)) y).mp hproj with hy | hy
            · exact Or.inl ⟨(r,t),hy.symm⟩
            · exact Or.inr ⟨L (r,t),⟨(r,t),rfl⟩,hy.symm⟩
    obtain ⟨h,L,hexpl,hzero,hboundary,hanchor,hπ,hedge,hcenter,hcover⟩ := hFull
    let f' : C(Metric.closedBall (0:Schoenflies.Plane) 1,S) := f.comp ⟨h,h.continuous⟩
    let z₀ : Metric.closedBall (0:Schoenflies.Plane) 1 := ⟨0,by simp⟩
    have honly' (z) : f' z ∈ M.cover.branch ↔ z=z₀ := by
      change f (h z) ∈ M.cover.branch ↔ z=z₀
      rw [honly]
      exact ⟨fun hz => h.injective (hz.trans hzero.symm),fun hz => hz ▸ hzero⟩
    have hnorm (t : Interval) : ‖(β t).val‖=1 := by
      have hh := Set.mem_range_self t (f := β)
      rw [hrange] at hh
      exact hh
    have hπ' (r t : Interval) : M.cover.projection (L (r,t))=
        f' (discRadialContraction z₀ r (β t)) := by
      rw [hπ]
      apply congrArg f
      apply Subtype.ext
      change (discRadialContraction m r (β t)).val =
        (h (discRadialContraction z₀ r (β t))).val
      rw [hexpl]
      have hval : (discRadialContraction z₀ r (β t)).val =
          (r:ℝ) • (β t).val := by simp [discRadialContraction,z₀]
      rw [hval, norm_smul, Real.norm_eq_abs, abs_of_nonneg r.property.1,
        hnorm, mul_one]
      change (1-(r:ℝ)) • m.val + (r:ℝ) • (β t).val =
        (r:ℝ) • (β t).val + (1-(r:ℝ)) • m.val
      exact add_comm _ _
    let J : C(OneMarkPolarStrip,E) := ⟨fun z => M.cover.sheetSelect z.2 (L z.1),by
      apply continuous_prod_of_discrete_right.mpr
      intro b
      cases b
      · simpa only [BranchedDoubleCover.sheetSelect,Bool.false_eq_true,↓reduceIte] using L.continuous
      · simpa only [BranchedDoubleCover.sheetSelect,↓reduceIte,Function.comp_def] using M.cover.deck.continuous.comp L.continuous⟩
    have hcollision (x y : OneMarkPolarStrip) : J x=J y ↔ oneMarkPolarRel x y :=
      M.cover.radial_sheet_collision_iff f' (hf.comp h.isEmbedding) honly'
        β hcoll hnorm L hπ' hedge hcenter x y
    have hJrange : Set.range J=Set.range L ∪ M.cover.deck '' Set.range L := by
      ext y
      constructor
      · rintro ⟨⟨z,b⟩,rfl⟩
        cases b
        · exact Or.inl ⟨z,rfl⟩
        · exact Or.inr ⟨L z,⟨z,rfl⟩,rfl⟩
      · rintro (⟨z,rfl⟩ | ⟨y,⟨z,rfl⟩,rfl⟩)
        · exact ⟨(z,false),rfl⟩
        · exact ⟨(z,true),rfl⟩
    let F : OneMarkPolarCell → E := Quot.lift J (fun x y hxy => (hcollision x y).mpr hxy)
    have hF : Continuous F := continuous_quot_lift _ J.continuous
    have hFinj : Function.Injective F := by
      intro x y
      induction x using Quot.inductionOn with | h x =>
        induction y using Quot.inductionOn with | h y =>
          intro hxy
          exact Quot.sound ((hcollision x y).mp hxy)
    have hFrange : Set.range F=M.cover.projection ⁻¹' Set.range f := by
      rw [← hcover,← hJrange]
      ext y
      constructor
      · rintro ⟨x,rfl⟩
        induction x using Quot.inductionOn with | h x => exact ⟨x,rfl⟩
      · rintro ⟨x,rfl⟩
        exact ⟨Quot.mk oneMarkPolarRel x,rfl⟩
    let G : OneMarkPolarCell → M.cover.projection ⁻¹' Set.range f :=
      fun x => ⟨F x,hFrange ▸ Set.mem_range_self x⟩
    have hG : Continuous G := hF.subtype_mk _
    have hGbij : Function.Bijective G := by
      constructor
      · intro x y hxy
        exact hFinj (congrArg Subtype.val hxy)
      · intro y
        have hyrange : y.val ∈ Set.range F := by rw [hFrange]; exact y.property
        obtain ⟨x,hx⟩ := hyrange
        exact ⟨x,Subtype.ext hx⟩
    let H : OneMarkPolarCell ≃ₜ M.cover.projection ⁻¹' Set.range f :=
      (Equiv.ofBijective G hGbij).toHomeomorphOfContinuousClosed hG hG.isClosedMap
    have hproj (x : OneMarkPolarStrip) :
        M.cover.projection (H (Quot.mk oneMarkPolarRel x)).val =
          f (discRadialContraction m x.1.1 (β x.1.2)) := by
      change M.cover.projection (M.cover.sheetSelect x.2 (L x.1))=_
      cases x.2 <;> simpa only [BranchedDoubleCover.sheetSelect,Bool.false_eq_true,
        ↓reduceIte,M.cover.projection_deck] using hπ x.1.1 x.1.2
    have hray (t : Interval) :
        Set.range (fun r : Interval => (H (Quot.mk oneMarkPolarRel ((r,t),false))).val) ∪
        Set.range (fun r : Interval => (H (Quot.mk oneMarkPolarRel ((r,t),true))).val) =
          M.cover.projection ⁻¹' Set.range (fun r : Interval =>
            f (discRadialContraction m r (β t))) := by
      ext y
      constructor
      · rintro (⟨r,rfl⟩ | ⟨r,rfl⟩)
        · exact ⟨r,(hproj ((r,t),false)).symm⟩
        · exact ⟨r,(hproj ((r,t),true)).symm⟩
      · rintro ⟨r,hr⟩
        have hp : M.cover.projection (L (r,t)) = M.cover.projection y :=
          (hπ r t).trans hr
        rcases (M.cover.fiber_pair (L (r,t)) y).mp hp with hy | hy
        · exact Or.inl ⟨r,hy.symm⟩
        · exact Or.inr ⟨r,hy.symm⟩
    let γ : C(Interval,E) := L.comp ⟨fun t => (1,t),by fun_prop⟩
    refine ⟨H,hanchor,hproj,hray,γ,?_,?_,?_,hanchor⟩
    · intro t; rfl
    · intro r t; rfl
    · intro t
      have hu : discRadialContraction m (1:Interval) (β t) = β t := by
        apply Subtype.ext
        change (1-(1:ℝ)) • m.val + (1:ℝ) • (β t).val = (β t).val
        simp
      have hp := hπ 1 t
      rw [hu] at hp
      exact hp

  have hMakeCell : ∀
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖<1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hends : β 0=β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β={z | ‖z.val‖=1})
    (η : C(Interval,E)) (hηπ : ∀ t, M.cover.projection (η t)=f (β (halfInterval t))),
    ∃ D : (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ≃ₜ M.cover.projection ⁻¹' Set.range f,
      (∀ t : Interval, (D (squareLeftSeam t)).val=η t) ∧
      (∀ t : Interval, (D (squareRightSeam t)).val=M.cover.deck (η t)) ∧
      ∃ γ : C(Interval,E), (∀ t, M.cover.projection (γ t)=f (β t)) ∧
        (∀ t, (D (unitSquareRaw (t,1))).val=γ (lateInterval t)) ∧
        (∀ t, (D (unitSquareRaw (unitInterval.symm t,0))).val=M.cover.deck (γ (lateInterval t))) ∧
        Set.range (fun t : Interval => (D (unitSquareRaw (t,⟨1/2,by norm_num⟩))).val) =
          M.cover.projection ⁻¹' Set.range (fun r : Interval =>
            f (discRadialContraction m r (β ⟨1/4,by norm_num⟩))) := by
    intro f hf m hm honly β hends hcoll hrange η hηπ
    let : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by simp⟩
    let : LocallyPathConnectedSpace Interval := (convex_Icc (0:ℝ) 1).locallyPathConnectedSpace
    have hnorm (t : Interval) : ‖(β t).val‖=1 := by
      have h := hrange ▸ Set.mem_range_self t (f:=β)
      exact h
    let b : C(Interval,S) := f.comp β
    have havoid (t) : b t ∉ M.cover.branch := by
      change f (β t) ∉ M.cover.branch
      rw [honly]
      intro he
      have hn := hnorm t
      rw [he] at hn
      linarith
    have h0 : M.cover.projection (η 0)=b 0 := by
      simpa only [b,ContinuousMap.comp_apply,halfInterval_zero] using hηπ 0
    obtain ⟨H,hanchor,hproj,hRay,γ,hH0,hDeck,hγπ,hγanchor⟩ :=
      hPolar f hf m hm honly β hends hcoll hrange (η 0) h0
    have hH1 (t : Interval) :
        (H (Quot.mk oneMarkPolarRel ((1,t),true))).val = M.cover.deck (γ t) :=
      (hDeck 1 t).trans (congrArg M.cover.deck (hH0 t))
    let σ : C(Interval,E) := γ.comp ⟨halfInterval,by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.div_const 2⟩
    have hση : σ=η := M.cover.boundary_lifts_eq_of_common_anchor σ η
      (fun t => (hγπ (halfInterval t)).trans (hηπ t).symm)
      (fun t => by change M.cover.projection (γ (halfInterval t)) ∉ M.cover.branch
                   rw [hγπ]; exact havoid (halfInterval t)) (by
        change γ (halfInterval 0)=η 0
        simpa only [halfInterval_zero] using hγanchor)
    have hp (t : Interval) : γ (halfInterval t)=η t :=
      congrFun (congrArg DFunLike.coe hση) t
    obtain ⟨K,hK⟩ := one_mark_polar_cell_square_chart
    let D := K.symm.trans H
    have hhalf (t : Interval) : (halfInterval t).val≤1/2 := by
      dsimp [halfInterval]; linarith [t.property.2]
    have hl (t : Interval) : K (Quot.mk oneMarkPolarRel ((1,halfInterval t),false))=squareLeftSeam t := by
      apply Subtype.ext
      rw [hK]
      simp only [polarSquareMap,polarSquareBoundary,Bool.false_eq_true,↓reduceIte,
        polarSquareHalf,ite_eq_left (hhalf t)]
      apply Prod.ext <;> dsimp [halfInterval,squareLeftSeam] <;> ring
    have hr (t : Interval) : K (Quot.mk oneMarkPolarRel ((1,halfInterval t),true))=squareRightSeam t := by
      apply Subtype.ext
      rw [hK]
      simp only [polarSquareMap,polarSquareBoundary,↓reduceIte,
        polarSquareHalf,ite_eq_left (hhalf t)]
      apply Prod.ext <;> dsimp [halfInterval,squareRightSeam] <;> ring
    refine ⟨D,?_,?_,γ,hγπ,?_,?_,?_⟩
    · intro t
      change (H (K.symm (squareLeftSeam t))).val=η t
      rw [← hl t,K.symm_apply_apply,hH0,hp]
    · intro t
      change (H (K.symm (squareRightSeam t))).val=M.cover.deck (η t)
      rw [← hr t,K.symm_apply_apply,hH1,hp]
  
    · intro t
      have hk : K (Quot.mk oneMarkPolarRel ((1,lateInterval t),false))=unitSquareRaw (t,1) := by
        apply Subtype.ext
        rw [hK]
        simp only [polarSquareMap,polarSquareBoundary,Bool.false_eq_true,↓reduceIte]
        unfold polarSquareHalf
        split_ifs with ht
        · have ht0 : t.val=0 := by dsimp [lateInterval] at ht; linarith [t.property.1]
          apply Prod.ext <;> dsimp [lateInterval,unitSquareRaw] <;> rw [ht0] <;> norm_num
        · apply Prod.ext <;> dsimp [lateInterval,unitSquareRaw] <;> ring
      change (H (K.symm (unitSquareRaw (t,1)))).val=γ (lateInterval t)
      rw [← hk,K.symm_apply_apply,hH0]
    · intro t
      have hk : K (Quot.mk oneMarkPolarRel ((1,lateInterval t),true))=unitSquareRaw (unitInterval.symm t,0) := by
        apply Subtype.ext
        rw [hK]
        simp only [polarSquareMap,polarSquareBoundary,↓reduceIte]
        unfold polarSquareHalf
        split_ifs with ht
        · have ht0 : t.val=0 := by dsimp [lateInterval] at ht; linarith [t.property.1]
          apply Prod.ext <;> dsimp [lateInterval,unitSquareRaw,unitInterval.symm] <;> rw [ht0] <;> norm_num
        · apply Prod.ext <;> dsimp [lateInterval,unitSquareRaw,unitInterval.symm] <;> ring
      change (H (K.symm (unitSquareRaw (unitInterval.symm t,0)))).val=M.cover.deck (γ (lateInterval t))
      rw [← hk,K.symm_apply_apply,hH1]
  
    · let angle : Interval := ⟨1/4,by norm_num⟩
      let mid : Interval := ⟨1/2,by norm_num⟩
      let lpar (r : Interval) : Interval := ⟨(1-r.val)/2,⟨by linarith [r.property.2],by linarith [r.property.1]⟩⟩
      let rpar (r : Interval) : Interval := ⟨(1+r.val)/2,⟨by linarith [r.property.1],by linarith [r.property.2]⟩⟩
      have hKl (r : Interval) : K (Quot.mk oneMarkPolarRel ((r,angle),false)) =
          unitSquareRaw (lpar r,mid) := by
        apply Subtype.ext
        rw [hK]
        simp only [polarSquareMap,polarSquareBoundary,Bool.false_eq_true,↓reduceIte,
          polarSquareHalf,show angle.val ≤ 1/2 by norm_num [angle],↓reduceIte]
        apply Prod.ext <;> dsimp [angle,lpar,mid,unitSquareRaw] <;> ring
      have hKr (r : Interval) : K (Quot.mk oneMarkPolarRel ((r,angle),true)) =
          unitSquareRaw (rpar r,mid) := by
        apply Subtype.ext
        rw [hK]
        simp only [polarSquareMap,polarSquareBoundary,↓reduceIte,
          polarSquareHalf,show angle.val ≤ 1/2 by norm_num [angle],↓reduceIte]
        apply Prod.ext <;> dsimp [angle,rpar,mid,unitSquareRaw] <;> ring
      have hDl (r : Interval) : (D (unitSquareRaw (lpar r,mid))).val =
          (H (Quot.mk oneMarkPolarRel ((r,angle),false))).val := by
        change (H (K.symm (unitSquareRaw (lpar r,mid)))).val = _
        rw [← hKl r,K.symm_apply_apply]
      have hDr (r : Interval) : (D (unitSquareRaw (rpar r,mid))).val =
          (H (Quot.mk oneMarkPolarRel ((r,angle),true))).val := by
        change (H (K.symm (unitSquareRaw (rpar r,mid)))).val = _
        rw [← hKr r,K.symm_apply_apply]
      have hmidrange :
          Set.range (fun t : Interval => (D (unitSquareRaw (t,mid))).val) =
          Set.range (fun r : Interval => (H (Quot.mk oneMarkPolarRel ((r,angle),false))).val) ∪
          Set.range (fun r : Interval => (H (Quot.mk oneMarkPolarRel ((r,angle),true))).val) := by
        ext y
        constructor
        · rintro ⟨t,ht⟩
          by_cases htm : t.val ≤ 1/2
          · let r : Interval := ⟨1-2*t.val,⟨by linarith,by linarith [t.property.1]⟩⟩
            have hp : lpar r = t := by apply Subtype.ext; dsimp [lpar,r]; ring
            left
            exact ⟨r,(hDl r).symm.trans (by rw [hp]; exact ht)⟩
          · let r : Interval := ⟨2*t.val-1,⟨by linarith,by linarith [t.property.2]⟩⟩
            have hp : rpar r = t := by apply Subtype.ext; dsimp [rpar,r]; ring
            right
            exact ⟨r,(hDr r).symm.trans (by rw [hp]; exact ht)⟩
        · rintro (⟨r,hr⟩ | ⟨r,hr⟩)
          · exact ⟨lpar r,(hDl r).trans hr⟩
          · exact ⟨rpar r,(hDr r).trans hr⟩
      change Set.range (fun t : Interval => (D (unitSquareRaw (t,mid))).val) = _
      rw [hmidrange,hRay angle]
  obtain ⟨D₀,hD₀L,hD₀R,γ₀,hγ₀Diskπ,hTop₀,hBottom₀,hMid₀⟩ :=
    hMakeCell d₀ hd₀ origin (by simp [origin]) hd₀Mark βd₀ hβd₀Ends
      hβd₀Coll hβd₀Range η hd₀η
  obtain ⟨D₁,hD₁L,hD₁R,γ₁,hγ₁Diskπ,hTop₁,hBottom₁,hMid₁⟩ :=
    hMakeCell d₁ hd₁ origin (by simp [origin]) hd₁Mark βd₁ hβd₁Ends
      hβd₁Coll hβd₁Range η hd₁η
  have hd₀Range : Set.range d₀ = Set.range f₀ := by
    change Set.range (f₀ ∘ B₀) = _
    rw [Set.range_comp,B₀.surjective.range_eq,Set.image_univ]
  have hd₁Range : Set.range d₁ = Set.range f₁ := by
    change Set.range (f₁ ∘ B₁) = _
    rw [Set.range_comp,B₁.surjective.range_eq,Set.image_univ]
  have hγ₀π (t : Interval) : M.cover.projection (γ₀ t) = f₀ (β₀ t) := by
    have hh := hγ₀Diskπ t
    change M.cover.projection (γ₀ t) = f₀ (B₀ (B₀.symm (β₀ t))) at hh
    rw [B₀.apply_symm_apply] at hh
    exact hh
  have hγ₁π (t : Interval) : M.cover.projection (γ₁ t) = f₁ (β₁ t) := by
    have hh := hγ₁Diskπ t
    change M.cover.projection (γ₁ t) = f₁ (B₁ (B₁.symm (β₁ t))) at hh
    rw [B₁.apply_symm_apply] at hh
    exact hh
  have hActualInter : (M.cover.projection ⁻¹' Set.range d₀) ∩
      (M.cover.projection ⁻¹' Set.range d₁) = Set.range η ∪ Set.range δ := by
    rw [hd₀Range,hd₁Range]
    exact hinter
  obtain ⟨H,hHr⟩ := square_pair_prescribed_seams_cylinder_edge_ranges
    (M.cover.projection ⁻¹' Set.range d₀) (M.cover.projection ⁻¹' Set.range d₁)
    D₀ D₁ η δ hD₀L hD₁L (fun t => (hD₀R t).trans (hδdeck t).symm)
    (fun t => (hD₁R t).trans (hδdeck t).symm) hActualInter
  have hu : (M.cover.projection ⁻¹' Set.range d₀) ∪
      (M.cover.projection ⁻¹' Set.range d₁) = M.cover.projection ⁻¹' N.closedSet := by
    rw [hd₀Range,hd₁Range,← Set.preimage_union,hbaseUnion,hfrange]
  let HT := H.trans (Homeomorph.setCongr hu)
  have hCore₀ : Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,mid))).val) =
      M.cover.projection ⁻¹' Set.range (f₀ ∘ ρ₀) := by
    rw [hMid₀]
    apply congrArg (fun X : Set S => M.cover.projection ⁻¹' X)
    exact congrArg Set.range (funext hρ₀Literal)
  have hCore₁ : Set.range (fun t : Interval => (D₁ (unitSquareRaw (t,mid))).val) =
      M.cover.projection ⁻¹' Set.range (f₁ ∘ ρ₁) := by
    rw [hMid₁]
    apply congrArg (fun X : Set S => M.cover.projection ⁻¹' X)
    exact congrArg Set.range (funext hρ₁Literal)
  have hCore₁rev : Set.range (fun t : Interval =>
      (D₁ (unitSquareRaw (unitInterval.symm t,mid))).val) =
      Set.range (fun t : Interval => (D₁ (unitSquareRaw (t,mid))).val) := by
    ext y
    constructor
    · rintro ⟨t,ht⟩; exact ⟨unitInterval.symm t,ht⟩
    · rintro ⟨t,ht⟩
      exact ⟨unitInterval.symm t,by simpa only [unitInterval.symm_symm] using ht⟩
  have hCoreH : Set.range (fun z : Circle => (HT (z,mid)).val) =
      M.cover.projection ⁻¹' a.image := by
    change Set.range (fun z : Circle => (H (z,mid)).val) = _
    rw [hHr mid]
    change Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,mid))).val) ∪
      Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,mid))).val) = _
    rw [hCore₁rev,hCore₀,hCore₁,hLiftedCoreCut]
  have he₀ : Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,1))).val) ∪
      Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,0))).val)=
      M.cover.projection ⁻¹' Set.range (fun t : Interval => f₀ (β₀ (lateInterval t))) := by
    have hbot : Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,0))).val)=
      Set.range (fun t : Interval => M.cover.deck (γ₀ (lateInterval t))) := by
      ext e
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,by simpa only [unitInterval.symm_symm] using (hBottom₀ (unitInterval.symm t)).symm⟩
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,hBottom₀ t⟩
    simp_rw [hTop₀]
    rw [hbot]
    exact M.cover.late_boundary_fiber_range (f₀.comp β₀) γ₀ hγ₀π
  have he₁ : Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,1))).val) ∪
      Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,0))).val)=
      M.cover.projection ⁻¹' Set.range (fun t : Interval => f₁ (β₁ (lateInterval t))) := by
    have htop : Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,1))).val)=
      Set.range (fun t : Interval => γ₁ (lateInterval t)) := by
      ext e
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,(hTop₁ _).symm⟩
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,by simpa only [unitInterval.symm_symm] using hTop₁ t⟩
    rw [htop]
    simp_rw [hBottom₁]
    exact M.cover.late_boundary_fiber_range (f₁.comp β₁) γ₁ hγ₁π
  have hout : Set.range (fun t : Interval => f₀ (β₀ (lateInterval t))) ∪
      Set.range (fun t : Interval => f₁ (β₁ (lateInterval t)))=
      f '' {z | z.val ∈ frontier K} := by
    ext y
    constructor
    · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
      · refine ⟨⟨(β₀ (lateInterval t)).val,hsubL (β₀ _).property⟩,?_,rfl⟩
        exact houterloops ▸ Or.inl ⟨t,rfl⟩
      · refine ⟨⟨(β₁ (lateInterval t)).val,hsubR (β₁ _).property⟩,?_,rfl⟩
        exact houterloops ▸ Or.inr ⟨t,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      have hz' : z.val ∈ Set.range (fun t : Interval => (β₀ (lateInterval t)).val) ∪
          Set.range (fun t : Interval => (β₁ (lateInterval t)).val) := houterloops.symm ▸ hz
      rcases hz' with ⟨t,ht⟩ | ⟨t,ht⟩
      · left; refine ⟨t,?_⟩
        apply congrArg f; exact Subtype.ext ht
      · right; refine ⟨t,?_⟩
        apply congrArg f; exact Subtype.ext ht
  let sphereAtlas := M.actualSphereSmoothAtlas
  letI : ChartedSpace Plane S := sphereAtlas.charts
  letI : IsManifold (𝓡 2) ∞ S := sphereAtlas.manifold
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI : ClosedSurface S := {}
  let d : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨fun z => (pair z : S),continuous_subtype_val.comp pair.continuous⟩
  have hd : IsEmbedding d := IsEmbedding.subtypeVal.comp pair.isEmbedding
  have hdRange : Set.range d = N.closedSet := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact (pair z).property
    · intro hx
      exact ⟨pair.symm ⟨x,hx⟩,congrArg Subtype.val (pair.apply_symm_apply ⟨x,hx⟩)⟩
  have hdClosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
  have hdFront : d '' {z | ‖z.val‖ = 1} = frontier N.closedSet := by
    rw [← hdRange,hdClosed.frontier_eq,LocalSurgery.embedded_surface_disk_interior_eq d hd]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨Set.mem_range_self z,?_⟩
      rintro ⟨w,hw,he⟩
      have he' : w = z := hd.injective he
      subst w
      have hzn : ‖z.val‖ < 1 := by
        simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hw
      change ‖z.val‖ = 1 at hz
      linarith
    · rintro ⟨⟨z,rfl⟩,hn⟩
      have hle : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using z.property
      have hzn : ‖z.val‖ = 1 := by
        apply le_antisymm hle
        by_contra h
        have hb : z.val ∈ Metric.ball (0 : Plane) 1 := by
          simp only [Metric.mem_ball,dist_zero_right]
          exact lt_of_not_ge h
        exact hn ⟨z,hb,rfl⟩
      exact ⟨z,hzn,rfl⟩
  let GW : Plane ≃ₜ (ℝ × ℝ) := h.trans e.toHomeomorph.symm
  have hWGlobal (z : Metric.closedBall (0 : Plane) 1) : (W z).val = GW z.val := by
    apply e.injective
    change e (W z).val = e (e.symm (h z.val))
    rw [e.apply_symm_apply]
    exact hWVal z
  have hWholeDisk (z : Metric.closedBall (0 : Plane) 1) : f (W z) = d z := by
    change (pair (u.symm (v (v.symm (u z)))) : S) = (pair z : S)
    rw [v.apply_symm_apply,u.symm_apply_apply]
  have hRectFront : f '' {z | z.val ∈ frontier K} = N.boundary.image := by
    rw [N.boundary_eq_frontier,← hdFront]
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      let z := W.symm x
      have hz : ‖z.val‖ = 1 := (hBoundaryNorm W GW hWGlobal z).mp (by
        rw [W.apply_symm_apply]; exact hx)
      refine ⟨z,hz,?_⟩
      exact (hWholeDisk z).symm.trans (congrArg f (W.apply_symm_apply x))
    · rintro ⟨z,hz,rfl⟩
      exact ⟨W z,(hBoundaryNorm W GW hWGlobal z).mpr hz,hWholeDisk z⟩
  refine ⟨HT,hCoreH,?_⟩
  change Set.range (fun z : Circle => (H (z,0)).val) ∪
    Set.range (fun z : Circle => (H (z,1)).val)=_
  rw [hHr 0,hHr 1]
  have hshuffle (A B C D : Set E) : (A ∪ B) ∪ (C ∪ D)=(C ∪ A) ∪ (D ∪ B) := by
    ext x; simp only [mem_union]; tauto
  change ((Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,0))).val)) ∪ Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,0))).val)) ∪
    ((Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,1))).val)) ∪ Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,1))).val))=_
  rw [hshuffle,he₀,he₁,← Set.preimage_union,hout,hRectFront]

end CurveComplex.HyperellipticModel
