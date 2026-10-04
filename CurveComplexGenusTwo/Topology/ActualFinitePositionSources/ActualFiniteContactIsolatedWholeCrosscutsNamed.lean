import CurveComplexGenusTwo.Filtration.Geometry.ActualCompactTimeCrosscutExtraction
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedTrimmedCrosscutAssembly
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteTransverseCrosscutRedrawing
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedPreparedFamilyCover
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedBothEndpointClearance

set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace CurveComplex.HyperellipticModel
open Set Metric Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem actualRelativeTargetAxisChart
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (P : Set S) (hPc : IsCompact P) (hbP : Disjoint (arcInterior M b) P)
    (p : S) (hp : p ∉ M.cover.branch) (hpP : p ∉ P) :
    ∃ e : OpenPartialHomeomorph S Plane, ∃ label : Bool,
      p ∈ e.source ∧ Disjoint e.source (M.cover.branch : Set S) ∧
      Disjoint e.source P ∧
      ∀ x ∈ e.source, x ∈ b.val.image ↔ label = true ∧ e x 0 = 0 := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let := (actualSphereSmoothAtlas M).charts
  by_cases hpb : p ∈ b.val.image
  · obtain ⟨τ,hτ⟩ := hpb
    have hτ0 : 0 < τ.val := by
      by_contra hn
      have he : τ = 0 := Subtype.ext (le_antisymm (le_of_not_gt hn) τ.property.1)
      exact hp (hτ ▸ (he ▸ b.val.start_marked))
    have hτ1 : τ.val < 1 := by
      by_contra hn
      have he : τ = 1 := Subtype.ext (le_antisymm τ.property.2 (le_of_not_gt hn))
      exact hp (hτ ▸ (he ▸ b.val.end_marked))
    let α : ℝ := τ.val/2
    let β : ℝ := (τ.val+1)/2
    have hα : 0 < α := by dsimp [α]; linarith
    have hαβ : α < β := by dsimp [α,β]; linarith
    have hβ : β < 1 := by dsimp [β]; linarith
    obtain ⟨e0,_,hcore,_,_,havoid,haxis,_⟩ :=
      actual_isotopy_core_crosscut_chart M b P hPc hbP (AmbientIsotopy.identity S)
        (fun _ _ _ => rfl) α β hα hαβ hβ 0
    have hp0 : p ∈ e0.source := by
      apply hcore
      refine ⟨τ.val,?_,?_⟩
      · dsimp [α,β]; constructor <;> linarith
      · simpa only [Function.comp_apply,Set.projIcc_val,AmbientIsotopy.identity,
          ContinuousMap.coe_mk] using hτ
    let L : Plane ≃ₜ ℝ × ℝ := ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
    let flip : Plane ≃ₜ Plane := (L.trans (Homeomorph.prodComm ℝ ℝ)).trans L.symm
    let e := e0.trans flip.toOpenPartialHomeomorph
    have hs : e.source = e0.source := by simp [e]
    refine ⟨e,true,hs.symm ▸ hp0,?_,?_,?_⟩
    · apply disjoint_left.mpr
      intro x hx hm
      exact (havoid x (hs ▸ hx)).1 hm
    · apply disjoint_left.mpr
      intro x hx hxP
      exact (havoid x (hs ▸ hx)).2 ⟨x,hxP,rfl⟩
    · intro x hx
      have he : e x 0 = e0 x 1 := rfl
      change x ∈ Set.range b.val.map ↔ true = true ∧ e x 0 = 0
      simpa only [he,eq_self,true_and,AmbientIsotopy.identity,ContinuousMap.coe_mk,
        Set.range_comp,Set.image_id] using haxis x (hs ▸ hx)
  · let forbidden : Set S := b.val.image ∪ ((M.cover.branch : Set S) ∪ P)
    have hc : IsClosed forbidden := (markedArc_image_compact b.val).isClosed.union
      (M.cover.branch.finite_toSet.isClosed.union hPc.isClosed)
    let e := (chartAt Plane p).restr forbiddenᶜ
    have hs : e.source = (chartAt Plane p).source ∩ forbiddenᶜ := by
      rw [OpenPartialHomeomorph.restr_source,hc.isOpen_compl.interior_eq]
    refine ⟨e,false,hs.symm ▸ ⟨mem_chart_source _ _,?_⟩,?_,?_,?_⟩
    · exact fun h => h.elim hpb (fun h => h.elim hp hpP)
    · exact disjoint_left.mpr (fun x hx hm => (hs ▸ hx).2 (Or.inr (Or.inl hm)))
    · exact disjoint_left.mpr (fun x hx hP => (hs ▸ hx).2 (Or.inr (Or.inr hP)))
    · intro x hx
      constructor
      · intro hb
        exact False.elim ((hs ▸ hx).2 (Or.inl hb))
      · rintro ⟨he,_⟩
        exact False.elim (Bool.false_ne_true he)




private theorem actualFiniteContactInteriorParameter
    (M : HyperellipticModel E S) (anchor a : EssentialMarkedArc M)
    (p : S) (hp : p ∈ ArcSurgery.crossings M anchor a) :
    ∃ t : Interval, 0 < t.val ∧ t.val < 1 ∧ a.val.map t = p := by
  obtain ⟨t,ht⟩ := hp.2.1
  refine ⟨t,?_,?_,ht⟩
  · by_contra hn
    have he : t=0 := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
    exact hp.2.2 (ht ▸ (he ▸ a.val.start_marked))
  · by_contra hn
    have he : t=1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt hn))
    exact hp.2.2 (ht ▸ (he ▸ a.val.end_marked))

private theorem actualInteriorContactIntervalInChart
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (p : S) (t : Interval) (ht0 : 0 < t.val) (ht1 : t.val < 1)
    (htp : a.val.map t = p) (e : OpenPartialHomeomorph S Plane)
    (hp : p ∈ e.source) :
    ∃ α β : ℝ, 0 < α ∧ α < t.val ∧ t.val < β ∧ β < 1 ∧
      (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc α β ⊆ e.source ∧
      (a.val.map ∘ projIcc 0 1 zero_le_one) α ≠ p ∧
      (a.val.map ∘ projIcc 0 1 zero_le_one) β ≠ p := by
  let f : ℝ → S := a.val.map ∘ projIcc 0 1 zero_le_one
  have hf : Continuous f := a.val.continuous.comp continuous_projIcc
  let V : Set ℝ := f ⁻¹' e.source ∩ Ioo 0 1
  have hV : IsOpen V := (e.open_source.preimage hf).inter isOpen_Ioo
  have htV : t.val ∈ V := by
    refine ⟨?_,ht0,ht1⟩
    change a.val.map (projIcc 0 1 zero_le_one t.val) ∈ e.source
    rw [projIcc_of_mem zero_le_one t.property]
    exact htp ▸ hp
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hV t.val htV
  let α := t.val-ε/2
  let β := t.val+ε/2
  have hαball : α ∈ Metric.ball t.val ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [α]; constructor <;> linarith
  have hβball : β ∈ Metric.ball t.val ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [β]; constructor <;> linarith
  have hαV := hball hαball
  have hβV := hball hβball
  have hαt : α < t.val := by dsimp [α]; linarith
  have htβ : t.val < β := by dsimp [β]; linarith
  refine ⟨α,β,hαV.2.1,hαt,htβ,hβV.2.2,?_,?_,?_⟩
  · rintro x ⟨u,hu,rfl⟩
    apply (hball ?_).1
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [α,β] at hu
    constructor <;> linarith [hu.1,hu.2]
  · intro he
    have hαI : α ∈ Icc (0:ℝ) 1 := ⟨hαV.2.1.le,hαV.2.2.le⟩
    rw [Function.comp_apply,projIcc_of_mem zero_le_one hαI] at he
    rcases a.val.injective_except_loop_closure _ t (he.trans htp.symm) with h | h | h
    · have hh := congrArg Subtype.val h
      exact (ne_of_lt hαt) hh
    · have hh := congrArg (fun u : Interval => u.val) h.2
      change t.val = 1 at hh
      linarith
    · have hh := congrArg (fun u : Interval => u.val) h.2
      change t.val = 0 at hh
      linarith
  · intro he
    have hβI : β ∈ Icc (0:ℝ) 1 := ⟨hβV.2.1.le,hβV.2.2.le⟩
    rw [Function.comp_apply,projIcc_of_mem zero_le_one hβI] at he
    rcases a.val.injective_except_loop_closure _ t (he.trans htp.symm) with h | h | h
    · have hh := congrArg Subtype.val h
      exact (ne_of_gt htβ) hh
    · have hh := congrArg (fun u : Interval => u.val) h.2
      change t.val = 1 at hh
      linarith
    · have hh := congrArg (fun u : Interval => u.val) h.2
      change t.val = 0 at hh
      linarith

private theorem actualFiniteContactDisjointAxisCharts
    (M : HyperellipticModel E S) (anchor a : EssentialMarkedArc M)
    (hf : (ArcSurgery.crossings M anchor a).Finite) :
    ∃ e : {p // p ∈ ArcSurgery.crossings M anchor a} → OpenPartialHomeomorph S Plane,
      (∀ k, k.val ∈ (e k).source) ∧
      (∀ k, Disjoint (e k).source (M.cover.branch : Set S)) ∧
      (∀ i j, i ≠ j → Disjoint (e i).source (e j).source) ∧
      (∀ k x, x ∈ (e k).source → (x ∈ anchor.val.image ↔ e k x 0=0)) ∧
      ∀ k x, x ∈ (e k).source →
        (x ∈ ArcSurgery.crossings M anchor a ↔ x=k.val) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let K := {p // p ∈ ArcSurgery.crossings M anchor a}
  letI : Fintype K := hf.fintype
  obtain ⟨U,hU,hdis⟩ := hf.t2_separation
  have hchart (k : K) : ∃ e : OpenPartialHomeomorph S Plane,
      k.val ∈ e.source ∧ Disjoint e.source (M.cover.branch : Set S) ∧
      e.source ⊆ U k.val ∧
      ∀ x ∈ e.source, x ∈ anchor.val.image ↔ e x 0=0 := by
    obtain ⟨e0,label,hke0,hm,_,haxis⟩ := actualRelativeTargetAxisChart
      M anchor ∅ isCompact_empty (disjoint_empty _) k.val k.property.1.2 (notMem_empty _)
    have hl : label=true := (haxis k.val hke0).mp k.property.1.1 |>.1
    let e := e0.restr (U k.val)
    have hs : e.source=e0.source ∩ U k.val := by
      rw [OpenPartialHomeomorph.restr_source,(hU k.val).2.interior_eq]
    refine ⟨e,hs.symm ▸ ⟨hke0,(hU k.val).1⟩,hm.mono_left (by intro x hx;exact (hs ▸ hx).1),
      (by intro x hx;exact (hs ▸ hx).2),?_⟩
    intro x hx
    change x ∈ anchor.val.image ↔ e0 x 0=0
    simpa only [hl,true_and] using haxis x (hs ▸ hx).1
  choose e hpoint hmarks hsub haxis using hchart
  refine ⟨e,hpoint,hmarks,?_,haxis,?_⟩
  · intro i j hij
    exact (hdis i.property j.property (fun he => hij (Subtype.ext he))).mono (hsub i) (hsub j)
  · intro k x hx
    constructor
    · intro hxc
      by_contra hne
      let j : K := ⟨x,hxc⟩
      have hkj : k ≠ j := fun he => hne (congrArg Subtype.val he).symm
      exact Set.disjoint_left.mp
        ((hdis k.property j.property (fun he => hkj (Subtype.ext he))))
        (hsub k hx) (hU x).1
    · intro he
      exact he.symm ▸ k.property

theorem actual_finite_contact_isolated_whole_crosscuts
    (M : HyperellipticModel E S) (anchor a : EssentialMarkedArc M)
    (hf : (ArcSurgery.crossings M anchor a).Finite) :
    ∃ α β : {p // p ∈ ArcSurgery.crossings M anchor a} → ℝ,
    ∃ e F : {p // p ∈ ArcSurgery.crossings M anchor a} → OpenPartialHomeomorph S Plane,
      (∀ k, 0 < α k ∧ α k < β k ∧ β k < 1) ∧
      (∀ k, (F k).source ⊆ (e k).source) ∧
      (∀ i j, i ≠ j → Disjoint (F i).source (F j).source) ∧
      (∀ k, Disjoint (e k).source (M.cover.branch : Set S)) ∧
      (∀ k, Plane.closedSquare 0 1 ⊆ (F k).target) ∧
      (∀ k, k.val ∈ (F k).source) ∧
      (∀ k, (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc (α k) (β k) ⊆ (F k).source) ∧
      (∀ k, F k ((a.val.map ∘ projIcc 0 1 zero_le_one) (α k))=Plane.mk (-1) 0 ∧
        F k ((a.val.map ∘ projIcc 0 1 zero_le_one) (β k))=Plane.mk 1 0) ∧
      (∀ k x, x ∈ (F k).source → (x ∈ a.val.image ↔ F k x 1=0)) ∧
      (∀ k, {x : S | x ∈ (F k).source ∧ F k x ∈ Plane.closedSquare 0 1} ∩ a.val.image =
        (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc (α k) (β k)) ∧
      (∀ k x, x ∈ (e k).source → (x ∈ anchor.val.image ↔ e k x 0=0)) ∧
      (∀ k x, x ∈ (F k).source →
        (x ∈ ArcSurgery.crossings M anchor a ↔ x=k.val)) ∧
      (∀ k, (a.val.map ∘ projIcc 0 1 zero_le_one) (α k) ∉ anchor.val.image ∧
        (a.val.map ∘ projIcc 0 1 zero_le_one) (β k) ∉ anchor.val.image) ∧
      Disjoint (arcInterior M a \ ⋃ k,
        (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc (α k) (β k)) anchor.val.image := by
  classical
  let K := {p // p ∈ ArcSurgery.crossings M anchor a}
  letI : Fintype K := hf.fintype
  obtain ⟨e,hpoint,hmarks,hdis,haxis,hisolate⟩ := actualFiniteContactDisjointAxisCharts M anchor a hf
  have hinterval (k : K) : ∃ t : Interval, ∃ α β : ℝ,
      0 < t.val ∧ t.val < 1 ∧ a.val.map t=k.val ∧
      0 < α ∧ α < t.val ∧ t.val < β ∧ β < 1 ∧
      (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc α β ⊆ (e k).source ∧
      (a.val.map ∘ projIcc 0 1 zero_le_one) α ≠ k.val ∧
      (a.val.map ∘ projIcc 0 1 zero_le_one) β ≠ k.val := by
    obtain ⟨t,ht0,ht1,ht⟩ := actualFiniteContactInteriorParameter M anchor a k.val k.property
    obtain ⟨α,β,hα,hαt,htβ,hβ,hsub,hane,hbne⟩ :=
      actualInteriorContactIntervalInChart M a k.val t ht0 ht1 ht (e k) (hpoint k)
    exact ⟨t,α,β,ht0,ht1,ht,hα,hαt,htβ,hβ,hsub,hane,hbne⟩
  choose t α β ht0 ht1 ht hα hαt htβ hβ hsub hane hbne using hinterval
  have hab (k : K) : α k < β k := (hαt k).trans (htβ k)
  have hcoresDis : ∀ i j : K, i ≠ j → Disjoint
      ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc (α i) (β i))
      ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc (α j) (β j)) := by
    intro i j hij
    exact (hdis i j hij).mono (hsub i) (hsub j)
  obtain ⟨F,hFsub,hFdis,hFsq,hFcore,hFends,hFaxis,hFexact⟩ :=
    actual_marked_finite_compatible_crosscuts M a K α β hab hα hβ e hsub hcoresDis
  have hkCore (k : K) : k.val ∈ (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc (α k) (β k) := by
    refine ⟨(t k).val,⟨(hαt k).le,(htβ k).le⟩,?_⟩
    rw [Function.comp_apply,projIcc_of_mem zero_le_one (t k).property]
    exact ht k
  refine ⟨α,β,e,F,(fun k => ⟨hα k,hab k,hβ k⟩),hFsub,hFdis,hmarks,hFsq,
    (fun k => hFcore k (hkCore k)),hFcore,hFends,hFaxis,hFexact,haxis,
    (fun k x hx => hisolate k x (hFsub k hx)),?_,?_⟩
  · intro k
    have endOff (z : ℝ) (hz : z ∈ Icc (α k) (β k)) (hne :
        (a.val.map ∘ projIcc 0 1 zero_le_one) z ≠ k.val) :
        (a.val.map ∘ projIcc 0 1 zero_le_one) z ∉ anchor.val.image := by
      intro hzanchor
      have hzI : z ∈ Icc (0:ℝ) 1 := ⟨(hα k).le.trans hz.1,hz.2.trans (hβ k).le⟩
      have hz0 : 0 < z := (hα k).trans_le hz.1
      have hz1 : z < 1 := hz.2.trans_lt (hβ k)
      have hzmarks : (a.val.map ∘ projIcc 0 1 zero_le_one) z ∉ M.cover.branch := by
        intro hm
        rcases a.val.marked_only_at_ends (projIcc 0 1 zero_le_one z) hm with he | he
        · have he' := congrArg Subtype.val he
          simp only [projIcc_of_mem zero_le_one hzI] at he'
          linarith
        · have he' := congrArg Subtype.val he
          simp only [projIcc_of_mem zero_le_one hzI] at he'
          linarith
      have hcontact : (a.val.map ∘ projIcc 0 1 zero_le_one) z ∈ ArcSurgery.crossings M anchor a :=
        ⟨⟨hzanchor,hzmarks⟩,⟨⟨projIcc 0 1 zero_le_one z,rfl⟩,hzmarks⟩⟩
      exact hne ((hisolate k _ (hsub k ⟨z,hz,rfl⟩)).mp hcontact)
    exact ⟨endOff (α k) (left_mem_Icc.mpr (hab k).le) (hane k),
      endOff (β k) (right_mem_Icc.mpr (hab k).le) (hbne k)⟩
  · apply disjoint_left.mpr
    rintro x ⟨hxa,hout⟩ hxanchor
    let k : K := ⟨x,⟨⟨hxanchor,hxa.2⟩,hxa⟩⟩
    exact hout (mem_iUnion.mpr ⟨k,hkCore k⟩)

end CurveComplex.HyperellipticModel
