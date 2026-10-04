import CurveComplexGenusTwo.Topology.ActualNonstandardCutRegion.ActualCutComponentSelection
import CurveComplexGenusTwo.Topology.ArcStraightening
import Schoenflies.Inversion
import ClassificationJordanCurve.Arcs
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import HalfspaceBoundaryPreservingOpenEmbedding

open Set Topology CurveComplex Schoenflies
open scoped Manifold ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

theorem original_chart_exterior_arc_in_ambient_disk_boundary_parallel
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let D₀ : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    ∀ (a : C(Interval, ↥Q)),
      IsEmbedding a →
      ((a 0).val ∈ B ∧ (a 1).val ∈ B) →
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ B) →
      ∀ (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S)),
        IsEmbedding d →
        D₀ ⊆ interior (Set.range d) →
        Set.range (fun t => (a t).val) ⊆ Set.range d →
        ∃ b : C(Interval, ↥Q), IsEmbedding b ∧ (∀ t, (b t).val ∈ B) ∧
          ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
            IsEmbedding e ∧
            e '' {u | u.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              Set.range a ∪ Set.range b := by
  classical
  intro Q B D₀ a ha hends hproper d hd hcapD haD
  let P := EuclideanSpace ℝ (Fin 2)
  let E := chartAt P x
  let p := E x
  let O : Set S := E.symm '' Metric.ball p R
  let K := Metric.closedBall (0 : P) 1
  let L : Set.range d ≃ₜ K := hd.toHomeomorph.symm
  let A : C(Interval, P) := ⟨fun t => (L ⟨(a t).val, haD ⟨t,rfl⟩⟩).val,
    continuous_subtype_val.comp (L.continuous.comp
      ((continuous_subtype_val.comp a.continuous).subtype_mk _))⟩
  have hAd (t : Interval) : d ⟨A t, (L ⟨(a t).val, haD ⟨t,rfl⟩⟩).property⟩ = (a t).val :=
    congrArg Subtype.val (hd.toHomeomorph.apply_symm_apply ⟨(a t).val,haD ⟨t,rfl⟩⟩)
  have hA : IsEmbedding A := IsEmbedding.subtypeVal.comp
    (L.isEmbedding.comp ((IsEmbedding.subtypeVal.comp ha).codRestrict _ _))
  let F : P ≃ₜ P :=
    (Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addLeft p)
  have hdist (z : P) : dist (F z) p = R * ‖z‖ := by
    change dist (p + R • z) p = R * ‖z‖
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have hFK (z : K) : F z.val ∈ Metric.closedBall p R := by
    rw [Metric.mem_closedBall, hdist]
    have hz : ‖z.val‖ ≤ 1 := by simpa only [K, Metric.mem_closedBall,dist_zero_right] using z.property
    nlinarith
  have hFin (z : K) : F z.val ∈ Metric.ball p R ↔ z.val ∈ Metric.ball (0:P) 1 := by
    simp only [Metric.mem_ball, hdist, dist_zero_right]
    constructor <;> intro h <;> nlinarith
  have hFbd (z : K) : F z.val ∈ Metric.sphere p R ↔ z.val ∈ Metric.sphere (0:P) 1 := by
    simp only [Metric.mem_sphere, hdist, dist_zero_right]
    constructor <;> intro h <;> nlinarith
  let cap : C(K,S) := ⟨fun z => E.symm (F z.val),
    E.symm.continuousOn.comp_continuous
      (F.continuous.comp continuous_subtype_val) (fun z => htarget (hFK z))⟩
  have hcap : IsEmbedding cap := E.symm.isEmbedding_restrict.comp
    ((F.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict _ (fun z => htarget (hFK z)))
  have hcapRange : Set.range cap = D₀ := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩; exact ⟨F z.val,hFK z,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      have hnorm : ‖F.symm z‖ ≤ 1 := by
        have hz' : R * ‖F.symm z‖ ≤ R := by
          rw [← hdist, F.apply_symm_apply]
          exact Metric.mem_closedBall.mp hz
        nlinarith
      exact ⟨⟨F.symm z,by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hnorm⟩,
        by change E.symm (F (F.symm z)) = _; rw [F.apply_symm_apply]⟩
  have hcapB : cap '' {z : K | z.val ∈ Metric.sphere (0:P) 1} = B := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩; exact ⟨F z.val,(hFbd z).mpr hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      have hnorm : ‖F.symm z‖ = 1 := by
        have hz' : R * ‖F.symm z‖ = R := by
          rw [← hdist, F.apply_symm_apply]
          exact Metric.mem_sphere.mp hz
        nlinarith
      refine ⟨⟨F.symm z,by simpa only [K,Metric.mem_closedBall,dist_zero_right,hnorm] using (le_refl (1:ℝ))⟩,?_,?_⟩
      · simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hnorm
      · change E.symm (F (F.symm z)) = _; rw [F.apply_symm_apply]
  have hcapO : cap '' {z : K | z.val ∈ Metric.ball (0:P) 1} = O := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩; exact ⟨F z.val,(hFin z).mpr hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      have hnorm : ‖F.symm z‖ < 1 := by
        have hz' : R * ‖F.symm z‖ < R := by
          rw [← hdist, F.apply_symm_apply]
          exact Metric.mem_ball.mp hz
        nlinarith
      refine ⟨⟨F.symm z,by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hnorm.le⟩,?_,?_⟩
      · simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hnorm
      · change E.symm (F (F.symm z)) = _; rw [F.apply_symm_apply]
  have hcapd (z : K) : cap z ∈ Set.range d :=
    interior_subset (hcapD (hcapRange ▸ Set.mem_range_self z))
  let cp : C(K,P) := ⟨fun z => (L ⟨cap z,hcapd z⟩).val,
    continuous_subtype_val.comp (L.continuous.comp (cap.continuous.subtype_mk _))⟩
  have hcp : IsEmbedding cp := IsEmbedding.subtypeVal.comp
    (L.isEmbedding.comp (hcap.codRestrict _ hcapd))
  have hcpd (z : K) : d ⟨cp z,(L ⟨cap z,hcapd z⟩).property⟩ = cap z :=
    congrArg Subtype.val (hd.toHomeomorph.apply_symm_apply ⟨cap z,hcapd z⟩)
  let circle := ClassificationJordanCurve.Arcs.circleHomeoSphere
  let r : C(Circle,P) := ⟨fun z => cp ⟨(circle z).val,Metric.sphere_subset_closedBall (circle z).property⟩,
    cp.continuous.comp (by fun_prop)⟩
  have hr : IsEmbedding r := hcp.comp
    ((IsEmbedding.subtypeVal.comp circle.isEmbedding).codRestrict _ _)
  let C₀ : Set P := Set.range r
  have hC₀ : IsJordanCurve C₀ := isJordanCurve_range_of_isEmbedding_circle r hr
  have hcpbd : cp '' {z : K | z.val ∈ Metric.sphere (0:P) 1} = C₀ := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨circle.symm ⟨z.val,hz⟩,?_⟩
      have hval : ((circle (circle.symm ⟨z.val,hz⟩)).val : P) = z.val :=
        congrArg (fun w : Metric.sphere (0:P) 1 => w.val) (circle.apply_symm_apply ⟨z.val,hz⟩)
      exact congrArg cp (Subtype.ext hval)
    · rintro ⟨z,rfl⟩
      exact ⟨⟨(circle z).val,Metric.sphere_subset_closedBall (circle z).property⟩,
        (circle z).property,rfl⟩
  have hcpRange : Set.range cp = inside C₀ ∪ C₀ :=
    embedded_disc_range_eq_closed_inside cp hcp C₀ hC₀ hcpbd
  let z₀ : K := ⟨0,by simp [K]⟩
  let c := cp z₀
  have hcnot : c ∉ C₀ := by
    intro hc
    obtain ⟨z,hz,hzc⟩ := hcpbd.symm ▸ hc
    have hz0 := hcp.injective hzc
    have : z.val = (0:P) := congrArg Subtype.val hz0
    change z.val ∈ Metric.sphere (0:P) 1 at hz
    rw [this] at hz
    simpa using hz
  have hc : c ∈ inside C₀ :=
    (hcpRange ▸ Set.mem_range_self z₀).resolve_right hcnot
  have hAdCp (t : Interval) (z : K) (heq : A t = cp z) : (a t).val = cap z := by
    rw [← hAd t, ← hcpd z]
    congr 1
    exact Subtype.ext heq
  have hAoff (t : Interval) : A t ≠ c := by
    intro h
    have haO : (a t).val ∈ O := by
      rw [← hcapO, hAdCp t z₀ h]
      exact ⟨z₀,by simp [z₀],rfl⟩
    exact (a t).property haO
  have hAC (t : Interval) : A t ∈ C₀ ↔ (a t).val ∈ B := by
    constructor
    · intro h
      obtain ⟨z,hz,he⟩ := hcpbd.symm ▸ h
      rw [← hcapB, hAdCp t z he.symm]
      exact ⟨z,hz,rfl⟩
    · intro h
      obtain ⟨z,hz,he⟩ := hcapB.symm ▸ h
      have heA : A t = cp z := by
        apply congrArg Subtype.val
        apply hd.injective
        exact (hAd t).trans he.symm |>.trans (hcpd z).symm
      rw [heA]
      exact hcpbd ▸ Set.mem_image_of_mem cp hz
  have hAoutside (t : Interval) (ht : t ∈ Ioo (0:Interval) 1) : A t ∈ outside C₀ := by
    have hn : A t ∉ Set.range cp := by
      rintro ⟨z,hz⟩
      have he : (a t).val = cap z := hAdCp t z hz.symm
      by_cases hzI : z.val ∈ Metric.ball (0:P) 1
      · have ho : cap z ∈ O := hcapO ▸ Set.mem_image_of_mem cap hzI
        exact (show (a t).val ∉ O from (a t).property) (he.symm ▸ ho)
      · have hzB : z.val ∈ Metric.sphere (0:P) 1 :=
          Metric.mem_sphere.mpr (le_antisymm z.property (not_lt.mp hzI))
        exact hproper t ht (he.symm ▸ (hcapB ▸ Set.mem_image_of_mem cap hzB))
    have hnotC : A t ∉ C₀ := fun h => hn (hcpRange.symm ▸ Or.inr h)
    have hparts : A t ∈ inside C₀ ∪ outside C₀ := by
      rw [inside_union_outside]; exact hnotC
    exact hparts.resolve_left
      (fun h => hn (hcpRange.symm ▸ Or.inl h))
  have arc_between (f : C(Interval,P)) (hf : IsEmbedding f) :
      IsArcBetween (Set.range f) (f 0) (f 1) := by
    let g : ℝ → P := fun t => f (Set.projIcc 0 1 (by norm_num) t)
    have hgt (t : Interval) : g t.val = f t := by
      dsimp [g]
      rw [Set.projIcc_of_mem _ t.property]
    refine ⟨g,(by dsimp [g]; fun_prop),?_,?_,?_,?_⟩
    · intro s hs t ht he
      have he' : f ⟨s,hs⟩ = f ⟨t,ht⟩ := by
        rw [← hgt ⟨s,hs⟩,← hgt ⟨t,ht⟩]; exact he
      exact congrArg Subtype.val (hf.injective he')
    · ext y
      constructor
      · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,(hgt ⟨t,ht⟩).symm⟩
      · rintro ⟨t,rfl⟩; exact ⟨t.val,t.property,hgt t⟩
    · exact hgt 0
    · exact hgt 1
  let Ai : C(Interval,P) := ⟨invert c ∘ A,
    (continuousOn_invert c).comp_continuous A.continuous
      (fun t => by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hAoff t)⟩
  have hAi : IsEmbedding Ai :=
    (Ai.continuous.isClosedEmbedding ((invert_injective c).comp hA.injective)).isEmbedding
  let Ci := invert c '' C₀
  have hCi : IsJordanCurve Ci := hC₀.invert_image hc.1
  have hAibd (t : Interval) : Ai t ∈ Ci ↔ A t ∈ C₀ := by
    change invert c (A t) ∈ invert c '' C₀ ↔ A t ∈ C₀
    constructor
    · rintro ⟨z,hz,he⟩
      exact (invert_injective c he) ▸ hz
    · exact Set.mem_image_of_mem (invert c)
  have hAiPD : Set.range Ai \ {Ai 0,Ai 1} ⊆ inside Ci := by
    rintro y ⟨⟨t,rfl⟩,hn⟩
    have ht0 : t ≠ 0 := fun h => hn (by simp [h])
    have ht1 : t ≠ 1 := fun h => hn (by simp [h])
    have ht : t ∈ Ioo (0:Interval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩
    have him := Set.mem_image_of_mem (invert c) (hAoutside t ht)
    rw [invert_image_outside (fun _ h => arc_complement h) hC₀ hc] at him
    exact him.1
  have hAi0 : Ai 0 ∈ Ci := (hAibd 0).mpr ((hAC 0).mpr hends.1)
  have hAi1 : Ai 1 ∈ Ci := (hAibd 1).mpr ((hAC 1).mpr hends.2)
  have hAi01 : Ai 0 ≠ Ai 1 := fun h => (show (0:Interval) ≠ 1 by norm_num) (hAi.injective h)
  obtain ⟨B₁,B₂,hcut⟩ := exists_isCutPair hCi hAi0 hAi1 hAi01
  have hcCi : c ∉ Ci := notMem_invert_image hc.1
  have hcAi : c ∉ Set.range Ai := by
    rintro ⟨t,ht⟩
    exact hAoff t (invert_eq_center_iff.mp ht)
  obtain ⟨hcover,hdisj,-,-,-,-,-,-,hcl₁,hcl₂⟩ :=
    general_crosscut_arbitrary_of_endpoints hCi (arc_between Ai hAi) hcut hAiPD
  have choose_side : ∃ J : Set P, IsArcBetween J (Ai 0) (Ai 1) ∧ J ⊆ Ci ∧
      c ∉ inside (J ∪ Set.range Ai) ∧
      inside (J ∪ Set.range Ai) ⊆ inside Ci := by
    have sub₁ : inside (B₁ ∪ Set.range Ai) ⊆ inside Ci := fun y hy =>
      (show y ∈ inside Ci \ Set.range Ai from hcover.symm ▸ Or.inl hy).1
    have sub₂ : inside (B₂ ∪ Set.range Ai) ⊆ inside Ci := fun y hy =>
      (show y ∈ inside Ci \ Set.range Ai from hcover.symm ▸ Or.inr hy).1
    by_cases hc₁ : c ∈ inside (B₁ ∪ Set.range Ai)
    · exact ⟨B₂,hcut.snd,hcut.snd_subset,
        fun h => Set.disjoint_left.mp hdisj hc₁ h,
        sub₂⟩
    · exact ⟨B₁,hcut.fst,hcut.fst_subset,hc₁,sub₁⟩
  obtain ⟨J,hJ,hJCi,hcJ,hinJ⟩ := choose_side
  obtain ⟨g,hgc,hgi,hgr,hg0,hg1⟩ := hJ
  let bI : C(Interval,P) := ⟨fun t => g t.val,
    continuousOn_iff_continuous_domRestrict.mp hgc⟩
  have hbI : IsEmbedding bI := (bI.continuous.isClosedEmbedding
    (fun s t h => Subtype.ext (hgi s.property t.property h))).isEmbedding
  have hbIr : Set.range bI = J := by
    rw [← hgr]
    ext y
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨t.val,t.property,rfl⟩
    · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,rfl⟩
  have hmeet (s t : Interval) (hst : Ai s = bI t) :
      (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
    have hsC : Ai s ∈ Ci := hJCi (hbIr ▸ ⟨t,hst.symm⟩)
    by_cases hs0 : s=0
    · left; refine ⟨hs0,hbI.injective ?_⟩
      change bI t = bI 0
      rw [show bI 0 = Ai 0 from hg0]
      exact hst.symm.trans (congrArg Ai hs0)
    by_cases hs1 : s=1
    · right; refine ⟨hs1,hbI.injective ?_⟩
      change bI t = bI 1
      rw [show bI 1 = Ai 1 from hg1]
      exact hst.symm.trans (congrArg Ai hs1)
    have hs : s ∈ Ioo (0:Interval) 1 :=
      ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),lt_of_le_of_ne s.property.2 hs1⟩
    exact False.elim ((inside_subset_compl (hAiPD ⟨⟨s,rfl⟩,by
      rintro (h | h)
      · exact hs0 (hAi.injective h)
      · rw [Set.mem_singleton_iff] at h; exact hs1 (hAi.injective h)⟩)) hsC)
  obtain ⟨cI,hcIr⟩ := exists_curve_of_two_arcs Ai bI hAi.injective hbI.injective hg0.symm hg1.symm hmeet
  have hcI : IsJordanCurve cI.image := isJordanCurve_range_of_isEmbedding_circle ⟨cI.map,cI.embedded.continuous⟩ cI.embedded
  have hcIJ : cI.image = J ∪ Set.range Ai := by rw [hcIr,hbIr,Set.union_comm]
  obtain ⟨q,hq,hqbd⟩ := jordan_curve_bounds_disc cI hcI
  have hqr : Set.range q = inside cI.image ∪ cI.image :=
    embedded_disc_range_eq_closed_inside q hq cI.image hcI hqbd
  have hcq : c ∉ Set.range q := by
    rw [hqr,hcIJ]
    rintro (h | hJ | hA)
    · exact hcJ h
    · exact hcCi (hJCi hJ)
    · exact hcAi hA
  have hqCi : Set.range q ⊆ Ci ∪ inside Ci := by
    rw [hqr,hcIJ]
    rintro y (h | hJ | hA)
    · exact Or.inr (hinJ h)
    · exact Or.inl (hJCi hJ)
    · obtain ⟨t,rfl⟩ := hA
      by_cases ht0 : t=0
      · exact Or.inl (ht0 ▸ hAi0)
      by_cases ht1 : t=1
      · exact Or.inl (ht1 ▸ hAi1)
      exact Or.inr (hAiPD ⟨⟨t,rfl⟩,by
        rintro (h | h)
        · exact ht0 (hAi.injective h)
        · rw [Set.mem_singleton_iff] at h; exact ht1 (hAi.injective h)⟩)
  have hqback : invert c '' Set.range q ⊆ C₀ ∪ outside C₀ := by
    rintro y ⟨z,hz,rfl⟩
    have hm : z ∈ (Ci ∪ inside Ci) \ {c} :=
      ⟨hqCi hz,fun h => hcq (h ▸ hz)⟩
    have he := (inversion_sides (fun _ h => arc_complement h) hC₀ hc).2.2.2.1
    exact he ▸ Set.mem_image_of_mem (invert c) hm
  let q₀ : C(K,P) := ⟨invert c ∘ q,
    (continuousOn_invert c).comp_continuous q.continuous
      (fun u => by
        change q u ≠ c
        intro h; exact hcq (h ▸ Set.mem_range_self u))⟩
  have hq₀ : IsEmbedding q₀ :=
    (q₀.continuous.isClosedEmbedding ((invert_injective c).comp hq.injective)).isEmbedding
  have hciInvcont : Continuous (invert c ∘ cI.map) :=
    (continuousOn_invert c).comp_continuous cI.embedded.continuous
      (fun z => by
        change cI.map z ≠ c
        intro he
        exact hcq (hqr.symm ▸ Or.inr ⟨z,he⟩))
  have hciInvemb : IsEmbedding (invert c ∘ cI.map) :=
    (hciInvcont.isClosedEmbedding ((invert_injective c).comp cI.embedded.injective)).isEmbedding
  let c₀ : Curve P := ⟨invert c ∘ cI.map,hciInvemb⟩
  have hc₀r : c₀.image = invert c '' cI.image := by
    simpa only [Curve.image,Set.image_univ] using Set.range_comp (invert c) cI.map
  have hq₀bd : q₀ '' {u : K | u.val ∈ Metric.sphere (0:P) 1} = c₀.image := by
    change (invert c ∘ q) '' _ = _
    rw [Set.image_comp,hqbd,hc₀r]
  have hq₀r : Set.range q₀ ⊆ C₀ ∪ outside C₀ := by
    change Set.range (invert c ∘ q) ⊆ _
    rw [Set.range_comp]
    exact hqback
  have hbIc (t : Interval) : bI t ≠ c := by
    intro h
    exact hcCi (h ▸ hJCi (hbIr ▸ Set.mem_range_self t))
  let b₀ : C(Interval,P) := ⟨invert c ∘ bI,
    (continuousOn_invert c).comp_continuous bI.continuous
      (fun t => by change bI t ≠ c; exact hbIc t)⟩
  have hb₀ : IsEmbedding b₀ :=
    (b₀.continuous.isClosedEmbedding ((invert_injective c).comp hbI.injective)).isEmbedding
  have hb₀C (t : Interval) : b₀ t ∈ C₀ := by
    have hm : bI t ∈ Ci := hJCi (hbIr ▸ Set.mem_range_self t)
    obtain ⟨z,hz,hze⟩ := hm
    change invert c (bI t) ∈ C₀
    rw [← hze,invert_invert]
    exact hz
  have hc₀split : c₀.image = Set.range A ∪ Set.range b₀ := by
    rw [hc₀r,hcIr,Set.image_union]
    have hbackA : invert c '' Set.range Ai = Set.range A := by
      change invert c '' Set.range (invert c ∘ A) = _
      rw [Set.range_comp,invert_image_invert_image]
    rw [hbackA]
    change Set.range A ∪ invert c '' Set.range bI = Set.range A ∪ Set.range (invert c ∘ bI)
    rw [Set.range_comp]
  have hc₀ : IsJordanCurve c₀.image :=
    isJordanCurve_range_of_isEmbedding_circle ⟨c₀.map,c₀.embedded.continuous⟩ c₀.embedded
  have hAK (t : Interval) : A t ∈ K := (L ⟨(a t).val,haD ⟨t,rfl⟩⟩).property
  have hb₀K (t : Interval) : b₀ t ∈ K := by
    obtain ⟨z,hz⟩ : b₀ t ∈ Set.range cp := hcpRange.symm ▸ Or.inr (hb₀C t)
    rw [← hz]
    exact (L ⟨cap z,hcapd z⟩).property
  let diskId : C(K,P) := ⟨Subtype.val,continuous_subtype_val⟩
  have hc₀K : c₀.image ⊆ Set.range diskId := by
    rw [hc₀split]
    rintro y (⟨t,rfl⟩ | ⟨t,rfl⟩)
    · exact ⟨⟨A t,hAK t⟩,rfl⟩
    · exact ⟨⟨b₀ t,hb₀K t⟩,rfl⟩
  obtain ⟨q₁,hq₁,hq₁bd,hq₁K⟩ :=
    LocalSurgery.curve_in_embedded_disk_bounds_subdisk c₀ diskId IsEmbedding.subtypeVal hc₀K
  have hq₁r : Set.range q₁ = Set.range q₀ := by
    rw [embedded_disc_range_eq_closed_inside q₁ hq₁ c₀.image hc₀ hq₁bd,
      embedded_disc_range_eq_closed_inside q₀ hq₀ c₀.image hc₀ hq₀bd]
  have hq₁mem (u : K) : q₁ u ∈ K := by
    obtain ⟨z,hz⟩ := hq₁K (Set.mem_range_self u)
    exact hz ▸ z.property
  have hq₁side (u : K) : q₁ u ∈ C₀ ∪ outside C₀ :=
    hq₀r (hq₁r ▸ Set.mem_range_self u)
  have hcpInterior (z : K) (hz : z.val ∈ Metric.ball (0:P) 1) : cp z ∈ inside C₀ := by
    have hzNot : cp z ∉ C₀ := by
      intro h
      obtain ⟨w,hw,hwe⟩ := hcpbd.symm ▸ h
      change w.val ∈ Metric.sphere (0:P) 1 at hw
      have he : w=z := hcp.injective hwe
      subst w
      exact (not_lt_of_ge (Metric.mem_sphere.mp hw).ge) (Metric.mem_ball.mp hz)
    exact (hcpRange ▸ Set.mem_range_self z).resolve_right hzNot
  let qD : C(K,K) := ⟨fun u => ⟨q₁ u,hq₁mem u⟩,q₁.continuous.subtype_mk _⟩
  let eS : C(K,S) := d.comp qD
  have heS : IsEmbedding eS := hd.comp (hq₁.codRestrict _ hq₁mem)
  have heSQ (u : K) : eS u ∈ Q := by
    change eS u ∉ O
    intro h
    obtain ⟨z,hz,hze⟩ := hcapO.symm ▸ h
    have he : q₁ u=cp z := by
      have he' : qD u = ⟨cp z,(L ⟨cap z,hcapd z⟩).property⟩ :=
        hd.injective (hze.symm.trans (hcpd z).symm)
      exact congrArg Subtype.val he'
    have hi : q₁ u ∈ inside C₀ := he.symm ▸ hcpInterior z hz
    rcases hq₁side u with hb | ho
    · exact hi.1 hb
    · exact Set.disjoint_left.mp disjoint_inside_outside hi ho
  let bD : C(Interval,K) := ⟨fun t => ⟨b₀ t,hb₀K t⟩,b₀.continuous.subtype_mk _⟩
  let bS : C(Interval,S) := d.comp bD
  have hbS : IsEmbedding bS := hd.comp (hb₀.codRestrict _ hb₀K)
  have hbSB (t : Interval) : bS t ∈ B := by
    obtain ⟨z,hz,hze⟩ := hcpbd.symm ▸ hb₀C t
    have he : bD t = ⟨cp z,(L ⟨cap z,hcapd z⟩).property⟩ := Subtype.ext hze.symm
    change d (bD t) ∈ B
    rw [he,hcpd]
    exact hcapB ▸ Set.mem_image_of_mem cap hz
  have hBQ : B ⊆ Q := by
    rintro y ⟨z,hz,rfl⟩ ⟨w,hw,he⟩
    have heq : w=z := E.symm.injOn
      (htarget (Metric.ball_subset_closedBall hw))
      (htarget (Metric.sphere_subset_closedBall hz)) he
    exact (not_lt_of_ge (Metric.mem_sphere.mp hz).ge) (heq ▸ Metric.mem_ball.mp hw)
  have hbSQ (t : Interval) : bS t ∈ Q := hBQ (hbSB t)
  let b : C(Interval,↥Q) := ⟨fun t => ⟨bS t,hbSQ t⟩,bS.continuous.subtype_mk _⟩
  let e : C(K,↥Q) := ⟨fun u => ⟨eS u,heSQ u⟩,eS.continuous.subtype_mk _⟩
  have hb : IsEmbedding b := hbS.codRestrict _ hbSQ
  have he : IsEmbedding e := heS.codRestrict _ heSQ
  refine ⟨b,hb,hbSB,e,he,?_⟩
  ext y
  constructor
  · rintro ⟨u,hu,rfl⟩
    have hm : q₁ u ∈ Set.range A ∪ Set.range b₀ :=
      hc₀split ▸ (hq₁bd ▸ Set.mem_image_of_mem q₁ hu)
    rcases hm with ⟨t,ht⟩ | ⟨t,ht⟩
    · left
      refine ⟨t,Subtype.ext ?_⟩
      change (a t).val = d (qD u)
      rw [← hAd t]
      exact congrArg d (Subtype.ext ht)
    · right
      refine ⟨t,Subtype.ext ?_⟩
      change d (bD t) = d (qD u)
      exact congrArg d (Subtype.ext ht)
  · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
    · have hm : A t ∈ q₁ '' {u : K | u.val ∈ Metric.sphere (0:P) 1} :=
        hq₁bd.symm ▸ (hc₀split.symm ▸ Or.inl (Set.mem_range_self t))
      obtain ⟨u,hu,heq⟩ := hm
      refine ⟨u,hu,Subtype.ext ?_⟩
      change d (qD u) = (a t).val
      rw [← hAd t]
      exact congrArg d (Subtype.ext heq)
    · have hm : b₀ t ∈ q₁ '' {u : K | u.val ∈ Metric.sphere (0:P) 1} :=
        hq₁bd.symm ▸ (hc₀split.symm ▸ Or.inr (Set.mem_range_self t))
      obtain ⟨u,hu,heq⟩ := hm
      refine ⟨u,hu,Subtype.ext ?_⟩
      change d (qD u) = d (bD t)
      exact congrArg d (Subtype.ext heq)

theorem actual_cut_collar_exterior_disk_component_model
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let D₀ : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    ∀ (n : ℕ) (a : Fin n → C(Interval, ↥Q)),
      (∀ i, IsEmbedding (a i)) →
      (∀ i, (a i 0).val ∈ B ∧ (a i 1).val ∈ B) →
      (∀ i t, t ∈ Set.Ioo (0 : Interval) 1 → (a i t).val ∉ B) →
      (∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j))) →
      let F : Set S := D₀ ∪ ⋃ i, Set.range (fun t => (a i t).val)
      ∀ C : CompactSideDoubledCut S Q B Fᶜ a,
        letI : TopologicalSpace C.Carrier := C.topology
        ∀ H : C(Interval × Circle, C.Carrier),
          IsEmbedding H →
          IsOpenEmbedding (fun z : Set.Ioo (0 : ℝ) 1 × Circle =>
            H (⟨z.1.val, ⟨z.1.property.1.le, z.1.property.2.le⟩⟩, z.2)) →
          (∀ t z, H (t, z) ∈ C.core ↔ t ≠ 0) →
          ∀ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S),
            IsEmbedding d →
            d '' {u | u.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              Set.range (fun z => (C.projection (H (⟨1/2, by norm_num⟩, z))).val) →
            Disjoint F (Set.range d) →
            let K := connectedComponent (H (0, 1))
            ∃ e : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ ↥K,
              ∀ u, (e u).val ∈ C.core ↔
                u.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  classical
  intro Q B D₀ n a hemb hend hinterior hpairwise F C
  letI : TopologicalSpace C.Carrier := C.topology
  letI : T2Space C.Carrier := C.hausdorff
  letI : CompactSpace C.Carrier := C.compact
  intro H hHembed hHopen hHcore d hd hboundary hdisjoint K
  let mid : Interval := ⟨1/2, by norm_num⟩
  have hmid : mid ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    norm_num [mid] at this
  have hBcap : B ⊆ D₀ :=
    Set.image_mono Metric.sphere_subset_closedBall
  have hboundaryF : ∀ w : C.Carrier, w ∉ C.core → (C.projection w).val ∈ F := by
    intro w hw
    have hex : w ∈ C.baseBoundary ∪
        ⋃ i, Set.range (C.side i false) ∪ Set.range (C.side i true) := by
      rw [← C.boundary_exhaustion]
      exact hw
    rcases hex with hb | hs
    · apply Or.inl
      apply hBcap
      exact C.base_boundary_image.subset (Set.mem_range_self (⟨w,hb⟩ : C.baseBoundary))
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hs
      rcases hi with ⟨t,rfl⟩ | ⟨t,rfl⟩ <;>
        exact Or.inr (Set.mem_iUnion.mpr ⟨i,t,congrArg Subtype.val (C.side_agrees i _ t).symm⟩)
  have hprojection : IsEmbedding (fun w : C.core => (C.projection w.val).val) := by
    have heq : (fun w : C.core => (C.projection w.val).val) =
        (Subtype.val : ↥(Fᶜ) → S) ∘ C.coreEquiv := by
      funext w
      exact C.core_agrees w
    rw [heq]
    exact IsEmbedding.subtypeVal.comp C.coreEquiv.isEmbedding
  have hdF : ∀ u, d u ∈ Fᶜ := fun u =>
    fun hu => Set.disjoint_left.mp hdisjoint hu (Set.mem_range_self u)
  let dF : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥(Fᶜ)) :=
    ⟨fun u => ⟨d u,hdF u⟩,d.continuous.subtype_mk _⟩
  let lift : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,C.Carrier) :=
    ⟨fun u => (C.coreEquiv.symm (dF u)).val,
      continuous_subtype_val.comp (C.coreEquiv.symm.continuous.comp dF.continuous)⟩
  have hliftcore : ∀ u, lift u ∈ C.core := fun u => (C.coreEquiv.symm (dF u)).property
  have hliftprojection : ∀ u, (C.projection (lift u)).val = d u := by
    intro u
    exact (C.core_agrees (C.coreEquiv.symm (dF u))).trans
      (congrArg Subtype.val (C.coreEquiv.apply_symm_apply (dF u)))
  have hliftembed : IsEmbedding lift :=
    IsEmbedding.subtypeVal.comp (C.coreEquiv.symm.isEmbedding.comp (hd.codRestrict _ _))
  have hliftboundary :
      lift '' {u | u.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range (fun z => H (mid,z)) := by
    ext w
    constructor
    · rintro ⟨u,hu,rfl⟩
      have hdu : d u ∈ Set.range (fun z => (C.projection (H (mid,z))).val) := by
        rw [← hboundary]
        exact ⟨u,hu,rfl⟩
      obtain ⟨z,hz⟩ := hdu
      refine ⟨z,?_⟩
      exact congrArg Subtype.val (hprojection.injective
        (a₁ := ⟨H (mid,z),(hHcore mid z).mpr hmid⟩)
        (a₂ := ⟨lift u,hliftcore u⟩) (hz.trans (hliftprojection u).symm))
    · rintro ⟨z,rfl⟩
      have hHz : (C.projection (H (mid,z))).val ∈
          d '' {u | u.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
        rw [hboundary]
        exact Set.mem_range_self z
      obtain ⟨u,hu,heq⟩ := hHz
      refine ⟨u,hu,?_⟩
      exact congrArg Subtype.val (hprojection.injective
        (a₁ := ⟨lift u,hliftcore u⟩)
        (a₂ := ⟨H (mid,z),(hHcore mid z).mpr hmid⟩) ((hliftprojection u).trans heq))
  have hfrontier : frontier (Set.range d) ⊆
      Set.range (fun z => (C.projection (H (mid,z))).val) := by
    rw [← hboundary]
    let f : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 → S :=
      fun z => d ⟨z.val,Metric.ball_subset_closedBall z.property⟩
    have hf : IsEmbedding f := hd.comp (IsEmbedding.inclusion Metric.ball_subset_closedBall)
    have hfopen : IsOpen (Set.range f) :=
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isOpen_range_of_isOpen_of_isEmbedding
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) Metric.isOpen_ball f hf
    have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
    intro y hy
    obtain ⟨z,rfl⟩ := hclosed.frontier_subset hy
    refine ⟨z, ?_, rfl⟩
    apply le_antisymm z.property
    apply not_lt.mp
    intro hz
    have hin : d z ∈ interior (Set.range d) :=
      hfopen.subset_interior_iff.mpr
        (by rintro v ⟨w,rfl⟩; exact Set.mem_range_self _) ⟨⟨z.val,hz⟩,rfl⟩
    exact hy.2 hin
  have hbelow : ∀ t : Interval, t < mid → ∀ z : Circle,
      (C.projection (H (t,z))).val ∉ Set.range d := by
    intro t ht z
    let p : C(Interval,S) :=
      ⟨fun s => (C.projection (H (s*t,z))).val,
        continuous_subtype_val.comp (C.projection.continuous.comp
          (H.continuous.comp ((continuous_id.mul continuous_const).prodMk continuous_const)))⟩
    have hpconn : IsPreconnected (Set.range p) :=
      isPreconnected_range p.continuous
    have hpavoid : Disjoint (Set.range p) (frontier (Set.range d)) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨s,rfl⟩ hy
      obtain ⟨v,hv⟩ := hfrontier hy
      by_cases hs : s*t = 0
      · have hpF : p s ∈ F := hboundaryF (H (s*t,z)) (by
          rw [hHcore]
          exact not_not.mpr hs)
        have hpD : p s ∈ Set.range d :=
          (isCompact_range d.continuous).isClosed.frontier_subset hy
        exact Set.disjoint_left.mp hdisjoint hpF hpD
      · have heq : H (mid,v) = H (s*t,z) :=
          congrArg Subtype.val (hprojection.injective
            (a₁ := ⟨H (mid,v),(hHcore mid v).mpr hmid⟩)
            (a₂ := ⟨H (s*t,z),(hHcore (s*t) z).mpr hs⟩) hv)
        have htime := congrArg Prod.fst (hHembed.injective heq)
        have hle : s*t ≤ t := by
          change s.val*t.val ≤ t.val
          nlinarith [s.property.2,t.property.1]
        exact (not_lt_of_ge (htime.trans_le hle)) ht
    rcases connected_cap_side (Set.range d) (Set.range p) hpconn hpavoid with hin | hout
    · have hzero : p 0 ∈ F := by
        apply hboundaryF
        rw [hHcore]
        simp
      exact False.elim (Set.disjoint_left.mp hdisjoint hzero
        (interior_subset (hin (Set.mem_range_self 0))))
    · have htout := interior_subset (hout (Set.mem_range_self 1))
      simpa only [p, ContinuousMap.coe_mk, one_mul, Set.mem_compl_iff] using htout
  have hbelowLift : ∀ t : Interval, t < mid → ∀ z : Circle,
      H (t,z) ∉ Set.range lift := by
    intro t ht z
    rintro ⟨u,hu⟩
    apply hbelow t ht z
    exact ⟨u,(hliftprojection u).symm.trans (congrArg (fun w => (C.projection w).val) hu)⟩
  let db : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,C.Carrier) :=
    ⟨fun u => lift ⟨u.val,Metric.sphere_subset_closedBall u.property⟩,
      lift.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hdb : IsEmbedding db :=
    hliftembed.comp (IsEmbedding.inclusion Metric.sphere_subset_closedBall)
  have hdbRange : Set.range db = Set.range (fun z => H (mid,z)) := by
    rw [← hliftboundary]
    ext w
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨⟨u.val,Metric.sphere_subset_closedBall u.property⟩,u.property,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u.val,hu⟩,rfl⟩
  have hmidembed : IsEmbedding (fun z => H (mid,z)) :=
    hHembed.comp (isEmbedding_prodMkRight mid)
  let clock : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ Circle :=
    hdb.toHomeomorph.trans ((Homeomorph.setCongr hdbRange).trans hmidembed.toHomeomorph.symm)
  have hclock : ∀ u, H (mid,clock u) = db u := by
    intro u
    have he := hmidembed.toHomeomorph.apply_symm_apply
      ((Homeomorph.setCongr hdbRange) (hdb.toHomeomorph u))
    exact congrArg Subtype.val he
  let band : Set C.Carrier := H '' {p | p.1 ≤ mid}
  have hseam : band ∩ Set.range lift = Set.range (fun z => H (mid,z)) := by
    ext w
    constructor
    · rintro ⟨⟨⟨t,z⟩,ht,rfl⟩,hD⟩
      change t ≤ mid at ht
      rcases lt_or_eq_of_le ht with hlt | heq
      · exact False.elim (hbelowLift t hlt z hD)
      · exact ⟨z,by rw [heq]⟩
    · rintro ⟨z,rfl⟩
      refine ⟨⟨(mid,z),show mid ≤ mid from le_rfl,rfl⟩,?_⟩
      have hmem : H (mid,z) ∈
          lift '' {u | u.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
        hliftboundary.symm.subset (Set.mem_range_self z)
      exact Set.image_subset_range _ _ hmem
  have hbandCompact : IsCompact band :=
    (IsClosed.isCompact (isClosed_le continuous_fst continuous_const)).image H.continuous
  have hbandConnected : IsConnected band := by
    have hprod : IsConnected ({p : Interval × Circle | p.1 ≤ mid}) := by
      have hbase : IsConnected (Set.Iic mid) :=
        ⟨⟨0,by exact unitInterval.nonneg mid⟩,isPreconnected_Iic⟩
      convert hbase.prod (isConnected_univ (α := Circle)) using 1
      ext p
      simp
    exact hprod.image H H.continuous.continuousOn
  let cap : Set C.Carrier := band ∪ Set.range lift
  have hcapCompact : IsCompact cap :=
    hbandCompact.union (isCompact_range lift.continuous)
  have hcapConnected : IsConnected cap := by
    letI : ConnectedSpace ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      isConnected_iff_connectedSpace.mp (Metric.isConnected_closedBall (by norm_num))
    have hliftConnected : IsConnected (Set.range lift) :=
      isConnected_range lift.continuous
    refine hbandConnected.union ?_ hliftConnected
    rw [hseam]
    exact Set.range_nonempty _
  have hcapComponent : cap ⊆ K := by
    have hbase : H (0,1) ∈ cap :=
      Or.inl ⟨(0,1),unitInterval.nonneg mid,rfl⟩
    exact hcapConnected.isPreconnected.subset_connectedComponent hbase
  have hcapBoundary : cap ∩ C.coreᶜ = Set.range (fun z => H (0,z)) := by
    ext w
    constructor
    · rintro ⟨hcap,hnot⟩
      rcases hcap with ⟨⟨t,z⟩,ht,rfl⟩ | ⟨u,rfl⟩
      · have ht0 : t = 0 := by
          by_contra hn
          exact hnot ((hHcore t z).mpr hn)
        exact ⟨z,by rw [ht0]⟩
      · exact False.elim (hnot (hliftcore u))
    · rintro ⟨z,rfl⟩
      refine ⟨Or.inl ⟨(0,z),unitInterval.nonneg mid,rfl⟩,?_⟩
      rw [Set.mem_compl_iff,hHcore]
      simp
  let disk := ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
  let inner : Set disk := {u | ‖u.val‖ ≤ 1/2}
  let outer : Set disk := {u | 1/2 ≤ ‖u.val‖}
  have hnotInner (u : disk) (hu : u ∉ inner) : 1/2 < ‖u.val‖ :=
    lt_of_not_ge (show ¬ ‖u.val‖ ≤ 1/2 from hu)
  have houtOfNot (u : disk) (hu : u ∉ inner) : u ∈ outer := (hnotInner u hu).le
  let small : C(↥inner,disk) := ⟨fun u => ⟨(2:ℝ) • u.val.val,by
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs]
    have hu : ‖u.val.val‖ ≤ 1/2 := u.property
    norm_num
    linarith⟩,by
      apply Continuous.subtype_mk
      change Continuous (fun u : ↥inner => (2:ℝ) • u.val.val)
      exact (continuous_const : Continuous (fun _ : ↥inner => (2:ℝ))).smul
        ((continuous_subtype_val : Continuous (fun u : disk => u.val)).comp continuous_subtype_val)⟩
  let polar : C(↥outer,↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
    ⟨fun u => ⟨‖u.val.val‖⁻¹ • u.val.val,by
      have hn : 0 < ‖u.val.val‖ := lt_of_lt_of_le (by norm_num) u.property
      rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']⟩,by
      apply Continuous.subtype_mk
      exact (((continuous_subtype_val.comp continuous_subtype_val).norm).inv₀
        (fun u => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) u.property))).smul
          (continuous_subtype_val.comp continuous_subtype_val)⟩
  let time : C(↥outer,Interval) := ⟨fun u => ⟨1-‖u.val.val‖,by
    have hu : ‖u.val.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using u.val.property
    exact ⟨sub_nonneg.mpr hu,by linarith [norm_nonneg u.val.val]⟩⟩,by
      apply Continuous.subtype_mk
      exact (continuous_const : Continuous (fun _ : ↥outer => (1:ℝ))).sub
        (((continuous_subtype_val : Continuous (fun u : disk => u.val)).comp continuous_subtype_val).norm)⟩
  let innerMap : C(↥inner,C.Carrier) := lift.comp small
  let outerMap : C(↥outer,C.Carrier) :=
    ⟨fun u => H (time u,clock (polar u)),
      H.continuous.comp (time.continuous.prodMk (clock.continuous.comp polar.continuous))⟩
  have hglueSeam : ∀ u : disk, ∀ hi : u ∈ inner, ∀ ho : u ∈ outer,
      innerMap ⟨u,hi⟩ = outerMap ⟨u,ho⟩ := by
    intro u hi ho
    have hn : ‖u.val‖ = 1/2 := le_antisymm hi ho
    have htime : time ⟨u,ho⟩ = mid := by
      apply Subtype.ext
      change 1-‖u.val‖ = 1/2
      rw [hn]
      norm_num
    change lift (small ⟨u,hi⟩) = H (time ⟨u,ho⟩,clock (polar ⟨u,ho⟩))
    rw [htime,hclock]
    change lift (small ⟨u,hi⟩) = lift ⟨(polar ⟨u,ho⟩).val,_⟩
    apply congrArg lift
    apply Subtype.ext
    change (2:ℝ) • u.val = ‖u.val‖⁻¹ • u.val
    rw [hn]
    norm_num
  let glued : disk → C.Carrier := fun u => if hu : u ∈ inner then
    innerMap ⟨u,hu⟩ else outerMap ⟨u,houtOfNot u hu⟩
  have hgluedInner : ∀ (u : disk) (hu : u ∈ inner), glued u = innerMap ⟨u,hu⟩ := by
    intro u hu
    simp only [glued,dif_pos hu]
  have hgluedOuter : ∀ (u : disk) (hu : u ∈ outer), glued u = outerMap ⟨u,hu⟩ := by
    intro u hu
    by_cases hi : u ∈ inner
    · rw [hgluedInner u hi]
      exact hglueSeam u hi hu
    · simp only [glued,dif_neg hi]
  have hgluedContinuous : Continuous glued := by
    have hi : ContinuousOn glued inner := by
      rw [continuousOn_iff_continuous_restrict]
      convert innerMap.continuous using 1
      funext u
      exact hgluedInner u.val u.property
    have ho : ContinuousOn glued outer := by
      rw [continuousOn_iff_continuous_restrict]
      convert outerMap.continuous using 1
      funext u
      exact hgluedOuter u.val u.property
    have hc := hi.union_of_isClosed ho (isClosed_le (by fun_prop) continuous_const)
      (isClosed_le continuous_const (by fun_prop))
    have hcover : inner ∪ outer = Set.univ := by
      ext u
      simp only [inner,outer,Set.mem_union,Set.mem_setOf_eq,Set.mem_univ,iff_true]
      exact le_total _ _
    rwa [hcover,continuousOn_univ] at hc
  have htimeLt : ∀ u : disk, ∀ hu : u ∉ inner,
      time ⟨u,houtOfNot u hu⟩ < mid := by
    intro u hu
    change 1-‖u.val‖ < 1/2
    have h : 1/2 < ‖u.val‖ := hnotInner u hu
    linarith
  have hgluedEmbed : IsEmbedding glued := by
    apply (Continuous.isClosedEmbedding hgluedContinuous ?_).isEmbedding
    intro u v huv
    by_cases hu : u ∈ inner <;> by_cases hv : v ∈ inner
    · rw [hgluedInner u hu,hgluedInner v hv] at huv
      have hh := congrArg Subtype.val (hliftembed.injective huv)
      apply Subtype.ext
      change (2:ℝ) • u.val = (2:ℝ) • v.val at hh
      exact (smul_right_injective _ (by norm_num : (2:ℝ)≠0)) hh
    · rw [hgluedInner u hu] at huv
      have hvout : v ∈ outer := houtOfNot v hv
      rw [hgluedOuter v hvout] at huv
      exact False.elim (hbelowLift (time ⟨v,hvout⟩) (htimeLt v hv)
        (clock (polar ⟨v,hvout⟩)) ⟨small ⟨u,hu⟩,huv⟩)
    · rw [hgluedInner v hv] at huv
      have huout : u ∈ outer := houtOfNot u hu
      rw [hgluedOuter u huout] at huv
      exact False.elim (hbelowLift (time ⟨u,huout⟩) (htimeLt u hu)
        (clock (polar ⟨u,huout⟩)) ⟨small ⟨v,hv⟩,huv.symm⟩)
    · have huout : u ∈ outer := houtOfNot u hu
      have hvout : v ∈ outer := houtOfNot v hv
      rw [hgluedOuter u huout,hgluedOuter v hvout] at huv
      have hh := hHembed.injective huv
      have hr := congrArg (fun p : Interval × Circle => p.1.val) hh
      have hp := congrArg Subtype.val (clock.injective (congrArg Prod.snd hh))
      have hnorm : ‖u.val‖ = ‖v.val‖ := by
        change 1-‖u.val‖ = 1-‖v.val‖ at hr
        linarith
      have hn : ‖u.val‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) huout)
      apply Subtype.ext
      change ‖u.val‖⁻¹ • u.val = ‖v.val‖⁻¹ • v.val at hp
      rw [← hnorm] at hp
      exact (smul_right_injective _ (inv_ne_zero hn)) hp
  have hgluedCore : ∀ u : disk, glued u ∈ C.core ↔
      u.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro u
    by_cases hi : u ∈ inner
    · rw [hgluedInner u hi]
      have hcore : innerMap ⟨u,hi⟩ ∈ C.core := hliftcore _
      have hn : ‖u.val‖ < 1 := lt_of_le_of_lt hi (by norm_num)
      exact iff_of_true hcore (by simpa only [Metric.mem_ball,dist_zero_right] using hn)
    · have ho : u ∈ outer := houtOfNot u hi
      rw [hgluedOuter u ho]
      change H (time ⟨u,ho⟩,clock (polar ⟨u,ho⟩)) ∈ C.core ↔ _
      rw [hHcore,Metric.mem_ball,dist_zero_right]
      have hbound : ‖u.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
      constructor
      · intro h
        apply lt_of_le_of_ne hbound
        intro he
        apply h
        apply Subtype.ext
        change 1-‖u.val‖ = 0
        rw [he]
        ring
      · intro h he
        have ht := congrArg Subtype.val he
        change 1-‖u.val‖ = 0 at ht
        linarith
  have hgluedRange : Set.range glued = cap := by
    apply Set.Subset.antisymm
    · rintro w ⟨u,rfl⟩
      by_cases hi : u ∈ inner
      · rw [hgluedInner u hi]
        exact Or.inr ⟨small ⟨u,hi⟩,rfl⟩
      · have ho := houtOfNot u hi
        rw [hgluedOuter u ho]
        exact Or.inl ⟨(time ⟨u,ho⟩,clock (polar ⟨u,ho⟩)),(htimeLt u hi).le,rfl⟩
    · intro w hw
      rcases hw with ⟨⟨t,z⟩,ht,rfl⟩ | ⟨u,rfl⟩
      · change t ≤ mid at ht
        let v := clock.symm z
        have hv : ‖v.val‖ = 1 := by
          simpa only [Metric.mem_sphere,dist_zero_right] using v.property
        have htn : 0 ≤ t.val := t.property.1
        have htt : t.val ≤ 1/2 := ht
        let u : disk := ⟨(1-t.val) • v.val,by
          rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
            abs_of_nonneg (by linarith : 0 ≤ 1-t.val),hv,mul_one]
          linarith⟩
        have hunorm : ‖u.val‖ = 1-t.val := by
          change ‖(1-t.val) • v.val‖ = 1-t.val
          rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith),hv,mul_one]
        have huout : u ∈ outer := by
          change 1/2 ≤ ‖u.val‖
          rw [hunorm]
          linarith
        refine ⟨u,?_⟩
        rw [hgluedOuter u huout]
        have htime : time ⟨u,huout⟩ = t := by
          apply Subtype.ext
          change 1-‖u.val‖ = t.val
          rw [hunorm]
          ring
        have hpolar : polar ⟨u,huout⟩ = v := by
          apply Subtype.ext
          change ‖u.val‖⁻¹ • u.val = v.val
          rw [hunorm]
          change (1-t.val)⁻¹ • ((1-t.val) • v.val) = v.val
          rw [smul_smul,inv_mul_cancel₀ (by linarith),one_smul]
        change H (time ⟨u,huout⟩,clock (polar ⟨u,huout⟩)) = H (t,z)
        rw [htime,hpolar]
        exact congrArg (fun y => H (t,y)) (clock.apply_symm_apply z)
      · have hu : ‖u.val‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
        let v : disk := ⟨(1/2:ℝ) • u.val,by
          rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs]
          norm_num
          linarith⟩
        have hvi : v ∈ inner := by
          change ‖(1/2:ℝ) • u.val‖ ≤ 1/2
          rw [norm_smul,Real.norm_eq_abs]
          norm_num
          linarith
        refine ⟨v,?_⟩
        rw [hgluedInner v hvi]
        change lift (small ⟨v,hvi⟩) = lift u
        apply congrArg lift
        apply Subtype.ext
        change (2:ℝ) • ((1/2:ℝ) • u.val) = u.val
        rw [smul_smul]
        norm_num
  let capModel : disk ≃ₜ cap :=
    hgluedEmbed.toHomeomorph.trans (Homeomorph.setCongr hgluedRange)
  have hcapModelCore : ∀ u : disk, (capModel u).val ∈ C.core ↔
      u.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := hgluedCore
  letI : ChartedSpace (EuclideanHalfSpace 2) C.Carrier := C.charts
  letI : IsManifold (𝓡∂ 2) 0 C.Carrier := C.manifold
  have hchartCore (e : OpenPartialHomeomorph C.Carrier (EuclideanHalfSpace 2))
      (w : C.Carrier) (hw : w ∈ e.source) :
      (e w).val 0 = 0 ↔ w ∉ C.core := by
    rw [C.core_eq_manifold_interior]
    change (e w).val 0 = 0 ↔ ¬ (𝓡∂ 2).IsInteriorPoint w
    rw [LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isInteriorPoint_iff_any_chart
      (𝓡∂ 2) hw,interior_range_modelWithCornersEuclideanHalfSpace]
    change (e w).val 0 = 0 ↔ ¬ 0 < (e w).val 0
    exact ⟨fun h => by rw [h]; exact lt_irrefl 0,
      fun h => le_antisymm (le_of_not_gt h) (e w).property⟩
  have hzeroOpen : ∀ z : Circle, H (0,z) ∈ interior cap := by
    intro z
    let P := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × Set.Ici (0:ℝ)
    let clamp : C(Set.Ici (0:ℝ),Interval) := ⟨fun r => ⟨min r.val 1,
      ⟨le_min r.property zero_le_one,min_le_right _ _⟩⟩,by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.min continuous_const⟩
    let params : C(P,Interval × Circle) :=
      ⟨fun p => (clamp p.2,clock p.1),
        (clamp.continuous.comp continuous_snd).prodMk (clock.continuous.comp continuous_fst)⟩
    let g : C(P,C.Carrier) := H.comp params
    let e₀ := unitCircleRadialChart (clock.symm z)
    let e₁ := chartAt (EuclideanHalfSpace 2) (H (0,z))
    let W : Set P := {p | p.2.val < 1/2} ∩ g ⁻¹' e₁.source
    have hW : IsOpen W :=
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const).inter
        (e₁.open_source.preimage g.continuous)
    let e := e₀.restr W
    have hsrc (p : e.source) : p.val.2.val < 1/2 ∧ g p.val ∈ e₁.source := by
      have hp := (e₀.restr_source' W hW).subset p.property
      exact hp.2
    have hparamTime (p : e.source) : (params p.val).1.val = p.val.2.val := by
      change min p.val.2.val 1 = p.val.2.val
      exact min_eq_left (by linarith [(hsrc p).1])
    let decode : C(Interval × Circle,P) :=
      ⟨fun p => (clock.symm p.2,⟨p.1.val,p.1.property.1⟩),by fun_prop⟩
    have hparamEmbed : IsEmbedding (fun p : e.source => params p.val) := by
      apply IsEmbedding.of_comp (params.continuous.comp continuous_subtype_val) decode.continuous
      convert (IsEmbedding.subtypeVal : IsEmbedding (fun p : e.source => p.val)) using 1
      funext p
      apply Prod.ext
      · exact clock.symm_apply_apply _
      · exact Subtype.ext (hparamTime p)
    let intoTarget : C(e.source,e₁.source) :=
      ⟨fun p => ⟨g p.val,(hsrc p).2⟩,
        (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hIntoEmbed : IsEmbedding intoTarget :=
      (hHembed.comp hparamEmbed).codRestrict _ _
    let f : C(e.target,EuclideanHalfSpace 2) :=
      ⟨fun u => e₁ (g ((e.toHomeomorphSourceTarget.symm u).val)),
        continuous_subtype_val.comp (e₁.toHomeomorphSourceTarget.continuous.comp
          (intoTarget.continuous.comp e.toHomeomorphSourceTarget.symm.continuous))⟩
    have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp
      (e₁.toHomeomorphSourceTarget.isEmbedding.comp
        (hIntoEmbed.comp e.toHomeomorphSourceTarget.symm.isEmbedding))
    have hecoord (p : P) : (e p).val 0 = p.2.val := by
      simp [e,e₀,unitCircleRadialChart,halfPlaneEuclidean_coord0]
    have hzero : ∀ u : e.target, (f u).val 0 = 0 ↔ u.val.val 0 = 0 := by
      intro u
      let p := e.toHomeomorphSourceTarget.symm u
      have hp0 : p.val.2.val = u.val.val 0 := by
        have hh := congrArg (fun q : e.target => q.val.val 0)
          (e.toHomeomorphSourceTarget.apply_symm_apply u)
        exact (hecoord p.val).symm.trans hh
      change (e₁ (g p.val)).val 0 = 0 ↔ _
      rw [hchartCore e₁ (g p.val) (hsrc p).2]
      change ¬ H (params p.val) ∈ C.core ↔ _
      rw [hHcore,not_not]
      constructor
      · intro ht
        have htv := congrArg Subtype.val ht
        change (params p.val).1.val = 0 at htv
        rw [hparamTime p,hp0] at htv
        exact htv
      · intro hu
        apply Subtype.ext
        change (params p.val).1.val = 0
        rw [hparamTime p,hp0,hu]
    have hfopen := halfspace_boundary_preserving_embedding_isOpenEmbedding
      e.target e.open_target f hf hzero
    have hrange : Set.range f ⊆ e₁.target := by
      rintro y ⟨u,rfl⟩
      exact e₁.map_source (hsrc (e.toHomeomorphSourceTarget.symm u)).2
    have hNopen : IsOpen (e₁.symm '' Set.range f) :=
      e₁.symm.isOpen_image_of_subset_source hfopen.isOpen_range hrange
    have hNcap : e₁.symm '' Set.range f ⊆ cap := by
      rintro w ⟨y,⟨u,rfl⟩,rfl⟩
      let p := e.toHomeomorphSourceTarget.symm u
      have hleft : e₁.symm (f u) = g p.val := e₁.left_inv (hsrc p).2
      rw [hleft]
      apply Or.inl
      refine ⟨params p.val,?_,rfl⟩
      change (params p.val).1 ≤ mid
      change (params p.val).1.val ≤ 1/2
      rw [hparamTime p]
      exact (hsrc p).1.le
    let p₀ : P := (clock.symm z,⟨0,by simp⟩)
    have hg0 : g p₀ = H (0,z) := by
      change H (clamp ⟨0,by simp⟩,clock (clock.symm z)) = H (0,z)
      rw [clock.apply_symm_apply]
      apply congrArg H
      apply Prod.ext
      · apply Subtype.ext
        norm_num [clamp]
      · rfl
    have hp0 : p₀ ∈ e.source := by
      rw [e₀.restr_source' W hW]
      refine ⟨unitCircleRadialChart_mem_source _ _,?_,?_⟩
      · change (0:ℝ)<1/2
        norm_num
      · change g p₀ ∈ e₁.source
        rw [hg0]
        exact mem_chart_source _ _
    have hmem : H (0,z) ∈ e₁.symm '' Set.range f := by
      let u := e.toHomeomorphSourceTarget ⟨p₀,hp0⟩
      refine ⟨f u,Set.mem_range_self u,?_⟩
      change e₁.symm (e₁ (g ((e.toHomeomorphSourceTarget.symm u).val))) = H (0,z)
      rw [show e.toHomeomorphSourceTarget.symm u = ⟨p₀,hp0⟩ from
        e.toHomeomorphSourceTarget.symm_apply_apply _,hg0]
      exact e₁.left_inv (mem_chart_source _ _)
    exact hNopen.subset_interior_iff.mpr hNcap hmem
  have hcoreOpen : ∀ u : disk, u.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      glued u ∈ interior cap := by
    let f : C(Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,C.core) :=
      ⟨fun u => ⟨glued ⟨u.val,Metric.ball_subset_closedBall u.property⟩,
        (hgluedCore _).mpr u.property⟩,
        (hgluedContinuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
    have hf : IsEmbedding f :=
      (hgluedEmbed.comp (IsEmbedding.inclusion Metric.ball_subset_closedBall)).codRestrict _ _
    let p : C(C.core,S) :=
      ⟨fun w => (C.projection w.val).val,
        continuous_subtype_val.comp (C.projection.continuous.comp continuous_subtype_val)⟩
    have hpf : IsEmbedding (p.comp f) := hprojection.comp hf
    have hpfopen : IsOpen (Set.range (p.comp f)) :=
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isOpen_range_of_isOpen_of_isEmbedding
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) Metric.isOpen_ball (p.comp f) hpf
    have hfrange : Set.range f = p ⁻¹' Set.range (p.comp f) := by
      ext w
      constructor
      · rintro ⟨u,rfl⟩
        exact Set.mem_range_self u
      · rintro ⟨u,hu⟩
        exact ⟨u,hprojection.injective hu⟩
    have hfopen : IsOpen (Set.range f) := hfrange ▸ hpfopen.preimage p.continuous
    have hNopen := C.core_open.isOpenMap_subtype_val (Set.range f) hfopen
    have hNcap : Subtype.val '' Set.range f ⊆ cap := by
      rintro w ⟨v,⟨u,rfl⟩,rfl⟩
      exact hgluedRange.subset (Set.mem_range_self _)
    intro u hu
    exact hNopen.subset_interior_iff.mpr hNcap
      ⟨f ⟨u.val,hu⟩,Set.mem_range_self _,rfl⟩
  have hcapOpen : IsOpen cap := by
    rw [← subset_interior_iff_isOpen]
    intro w hw
    obtain ⟨u,rfl⟩ := hgluedRange.symm.subset hw
    by_cases hu : glued u ∈ C.core
    · exact hcoreOpen u ((hgluedCore u).mp hu)
    · obtain ⟨z,hz⟩ := hcapBoundary.subset ⟨hgluedRange.subset (Set.mem_range_self u),hu⟩
      exact hz ▸ hzeroOpen z
  have hcapEq : cap = K := by
    apply Set.Subset.antisymm hcapComponent
    exact (show IsClopen cap from ⟨hcapCompact.isClosed,hcapOpen⟩).connectedComponent_subset
      (Or.inl ⟨(0,1),unitInterval.nonneg mid,rfl⟩)
  refine ⟨capModel.trans (Homeomorph.setCongr hcapEq),?_⟩
  exact hcapModelCore

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
