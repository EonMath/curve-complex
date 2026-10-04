import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassMarkedSweep
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualContinuousSweepConcatenation
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- The ORIGINAL nonloop target constructs its own embedded marked parallel
sweep, with literal endpoints fixed and terminal interior off its entire trace.
This is selector geometry, not an asserted stationary-anchor minimum move. -/
private theorem actual_rl_nonloop_marked_parallel_sweep_private
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) :
    ∃ F : C(Interval × Interval,S),
      (∀ t, F (0,t) = a.val.map t) ∧
      (∀ τ, Function.Injective (fun t => F (τ,t))) ∧
      (∀ τ, F (τ,0) = a.val.map 0 ∧ F (τ,1) = a.val.map 1) ∧
      (∀ τ t, t ≠ 0 → t ≠ 1 → F (τ,t) ∉ (M.cover.branch : Set S)) ∧
      ∀ t, t ≠ 0 → t ≠ 1 → F (1,t) ∉ a.val.image := by
  let : T2Space S := M.sphere.symm.t2Space
  let := (actualSphereSmoothAtlas M).charts
  let af : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  have haf : IsEmbedding af :=
    (af.continuous.isClosedEmbedding (NonLoopArc.injective ⟨a.val,ha⟩)).isEmbedding
  let carrier : Set S := ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ
  have hcarrier : IsOpen carrier :=
    (M.cover.branch.finite_toSet.subset sdiff_subset).isClosed.isOpen_compl
  have htrace : range af ⊆ carrier := by
    rintro _ ⟨t,rfl⟩ ⟨hm,hn⟩
    rcases a.val.marked_only_at_ends t hm with rfl | rfl
    · exact hn (by simp [af])
    · exact hn (by simp [af])
  obtain ⟨B,hB,hcenter,hBcarrier⟩ := CurveComplex.source_whole_embedded_arc_strip af haf
    carrier hcarrier htrace
  let y : Interval × Interval → Set.Icc (-1:ℝ) 1 := fun z =>
    ⟨z.1.val*z.2.val*(1-z.2.val)/4,by
      have h0 := z.1.property.1
      have h1 := z.1.property.2
      have ht0 := z.2.property.1
      have ht1 := z.2.property.2
      have hprod : 0 ≤ z.2.val*(1-z.2.val) := mul_nonneg ht0 (by linarith)
      have hprod1 : z.2.val*(1-z.2.val) ≤ 1 := by nlinarith [sq_nonneg (z.2.val-1/2)]
      constructor <;> nlinarith⟩
  let F : C(Interval × Interval,S) := ⟨fun z => B (z.2,y z),hB.continuous.comp (by
    apply Continuous.prodMk continuous_snd
    apply Continuous.subtype_mk
    fun_prop)⟩
  have hy0 (t : Interval) : y (0,t) = ⟨0,by norm_num⟩ := by
    apply Subtype.ext
    simp [y]
  have hyends (τ : Interval) : y (τ,0) = ⟨0,by norm_num⟩ ∧ y (τ,1) = ⟨0,by norm_num⟩ := by
    constructor <;> apply Subtype.ext <;> simp [y]
  refine ⟨F,?_,?_,?_,?_,?_⟩
  · intro t
    change B (t,y (0,t))=a.val.map t
    rw [hy0,hcenter]
    rfl
  · intro τ s t he
    exact congrArg Prod.fst (hB.injective he)
  · intro τ
    constructor
    · change B (0,y (τ,0))=a.val.map 0
      rw [(hyends τ).1,hcenter]; rfl
    · change B (1,y (τ,1))=a.val.map 1
      rw [(hyends τ).2,hcenter]; rfl
  · intro τ t ht0 ht1 hm
    have he : F (τ,t) ∈ ({a.val.map 0,a.val.map 1} : Set S) := by
      by_contra hn
      exact hBcarrier (mem_range_self (t,y (τ,t))) ⟨hm,hn⟩
    rcases he with he | he
    · exact ht0 (congrArg Prod.fst (hB.injective (he.trans (hcenter 0).symm)))
    · exact ht1 (congrArg Prod.fst (hB.injective (he.trans (hcenter 1).symm)))
  · intro t ht0 ht1 ⟨s,hs⟩
    have he : B (t,y (1,t)) = B (s,⟨0,by norm_num⟩) := hs.symm.trans (hcenter s).symm
    have hy := congrArg (fun z : Interval × Set.Icc (-1:ℝ) 1 => z.2.val) (hB.injective he)
    have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (fun hh => ht0 (Subtype.ext hh.symm))
    have htlt : t.val < 1 := lt_of_le_of_ne t.property.2 (fun hh => ht1 (Subtype.ext hh))
    change 1*t.val*(1-t.val)/4=0 at hy
    nlinarith [mul_pos htpos (sub_pos.mpr htlt)]
end
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- ORIGINAL same-class nonloop data construct an embedded endpoint-fixed sweep
of original b to a parallel of original a whose interior is entirely off a.
No adjacency, alternate representative, homotopy or terminal push-off is input.
This supplies selector geometry, not a stationary-anchor minimum move. -/
private theorem actual_rl_same_class_target_avoiding_nonloop_sweep_private
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) (hb : b.val.map 0 ≠ b.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b) :
    ∃ K : C(Interval × Interval,S),
      (∀ t, K (0,t)=b.val.map t) ∧
      (∀ τ, Function.Injective (fun t => K (τ,t))) ∧
      (∀ τ, K (τ,0)=b.val.map 0 ∧ K (τ,1)=b.val.map 1) ∧
      (∀ τ t, t ≠ 0 → t ≠ 1 → K (τ,t) ∉ (M.cover.branch : Set S)) ∧
      ∀ t, t ≠ 0 → t ≠ 1 → K (1,t) ∉ a.val.image := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨F,hFzero,hcollision,hFends,hFmarks,hterminalImage⟩ :=
    actual_same_class_marked_arc_sweep M b a hclass.symm
  have hFinj (τ : Interval) : Function.Injective (fun t => F (τ,t)) := by
    intro s t he
    rcases hcollision τ s t he with hh | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hh
    · exact False.elim (hb ((hFends τ).1.symm.trans (he.trans (hFends τ).2)))
    · exact False.elim (hb ((hFends τ).1.symm.trans (he.symm.trans (hFends τ).2)))
  let af : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  have haf : IsEmbedding af := (af.continuous.isClosedEmbedding (NonLoopArc.injective ⟨a.val,ha⟩)).isEmbedding
  have hFterminal (t : Interval) : F (1,t) ∈ range af := by
    change F (1,t) ∈ a.val.image
    rw [← hterminalImage]
    exact mem_range_self t
  let L : C(Interval,range af) := ⟨fun t => ⟨F (1,t),hFterminal t⟩,
    (F.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk hFterminal⟩
  let φ : C(Interval,Interval) := ⟨fun t => haf.toHomeomorph.symm (L t),
    haf.toHomeomorph.symm.continuous.comp L.continuous⟩
  have hcoord (t : Interval) : a.val.map (φ t)=F (1,t) :=
    congrArg Subtype.val (haf.toHomeomorph.apply_symm_apply (L t))
  have hφinj : Function.Injective φ := by
    intro s t he
    apply hFinj 1
    change F (1,s)=F (1,t)
    rw [← hcoord,← hcoord,he]
  have hφinterior (t : Interval) (ht0 : t≠0) (ht1 : t≠1) : φ t≠0 ∧ φ t≠1 := by
    constructor
    · intro he
      apply hFmarks 1 t ht0 ht1
      rw [← hcoord,he]
      exact a.val.start_marked
    · intro he
      apply hFmarks 1 t ht0 ht1
      rw [← hcoord,he]
      exact a.val.end_marked
  have hφends : (φ 0=0 ∨ φ 0=1) ∧ (φ 1=0 ∨ φ 1=1) := by
    constructor
    · apply a.val.marked_only_at_ends
      rw [hcoord,(hFends 1).1]
      exact b.val.start_marked
    · apply a.val.marked_only_at_ends
      rw [hcoord,(hFends 1).2]
      exact b.val.end_marked
  obtain ⟨G,hGzero,hGinj,hGends,hGmarks,hGterminal⟩ := actual_rl_nonloop_marked_parallel_sweep_private M a ha
  let Q : C(Interval × Interval,S) :=
    ⟨fun z => G (z.1,φ z.2),G.continuous.comp (continuous_fst.prodMk (φ.continuous.comp continuous_snd))⟩
  have hQzero (t : Interval) : Q (0,t)=F (1,t) := (hGzero (φ t)).trans (hcoord t)
  have hQinj (τ : Interval) : Function.Injective (fun t => Q (τ,t)) :=
    (hGinj τ).comp hφinj
  have hQends (τ : Interval) : Q (τ,0)=b.val.map 0 ∧ Q (τ,1)=b.val.map 1 := by
    constructor
    · change G (τ,φ 0)=b.val.map 0
      rcases hφends.1 with h0 | h1
      · rw [h0,(hGends τ).1]
        exact (congrArg a.val.map h0).symm.trans ((hcoord 0).trans (hFends 1).1)
      · rw [h1,(hGends τ).2]
        exact (congrArg a.val.map h1).symm.trans ((hcoord 0).trans (hFends 1).1)
    · change G (τ,φ 1)=b.val.map 1
      rcases hφends.2 with h0 | h1
      · rw [h0,(hGends τ).1]
        exact (congrArg a.val.map h0).symm.trans ((hcoord 1).trans (hFends 1).2)
      · rw [h1,(hGends τ).2]
        exact (congrArg a.val.map h1).symm.trans ((hcoord 1).trans (hFends 1).2)
  obtain ⟨K,hKzero,hKone,hKslices⟩ := CurveComplex.actual_continuous_sweep_concatenation F Q
    (fun t => (hQzero t).symm)
  refine ⟨K,(fun t => (hKzero t).trans (hFzero t)),?_,?_,?_,?_⟩
  · intro τ s t he
    rcases hKslices τ with ⟨σ,hσ⟩ | ⟨σ,hσ⟩
    · exact hFinj σ ((hσ s).symm.trans (he.trans (hσ t)))
    · exact hQinj σ ((hσ s).symm.trans (he.trans (hσ t)))
  · intro τ
    rcases hKslices τ with ⟨σ,hσ⟩ | ⟨σ,hσ⟩
    · exact ⟨(hσ 0).trans (hFends σ).1,(hσ 1).trans (hFends σ).2⟩
    · exact ⟨(hσ 0).trans (hQends σ).1,(hσ 1).trans (hQends σ).2⟩
  · intro τ t ht0 ht1
    rcases hKslices τ with ⟨σ,hσ⟩ | ⟨σ,hσ⟩
    · rw [hσ t]; exact hFmarks σ t ht0 ht1
    · rw [hσ t]
      exact hGmarks σ (φ t) (hφinterior t ht0 ht1).1 (hφinterior t ht0 ht1).2
  · intro t ht0 ht1
    rw [hKone t]
    exact hGterminal (φ t) (hφinterior t ht0 ht1).1 (hφinterior t ht0 ht1).2
end
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.actual_rl_nonloop_marked_parallel_sweep_private
#print axioms CurveComplex.HyperellipticModel.actual_rl_same_class_target_avoiding_nonloop_sweep_private
