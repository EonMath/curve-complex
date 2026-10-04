import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalActualPlanarJordanNullhomotopyVerifiedSnapshot
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalActualOrientableModelCrossingVerifiedSnapshot
import CurveComplexGenusTwo.Topology.ActualCrosscapGeometry.NonorientableCrossing
import CurveComplexGenusTwo.Topology.ActualBoundaryModels.ZeroHandleClosedDisc
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalActualSurfaceAxisChartProof
import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverExistence
import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverCount
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalFirstDiskHalfLevelManifoldProof
import CurveComplexGenusTwo.Topology.FrontierCircle.BandLocal
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalProjectiveAntipodalStatement
import Lean
import CurveComplexGenusTwo.Topology.ActualGenusZeroPlanarity.ActualGenusZeroPlanarity
import ClassificationOfSurfaces.Moise.ChartInduction
import ClassificationOfSurfaces.EvalStatement
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import ClassificationOfSurfaces.FiniteCyclicCancellation
import ClassificationOfSurfaces.FiniteCyclicCanonicalRealization
import ClassificationOfSurfaces.FiniteCyclicWordReductionCore
import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import ClassificationJordanCurve.Arcs
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe

import ClassificationOfSurfaces.SphereQuotientHomeomorph
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import CurveComplexGenusTwo.Topology.SurfaceRecognition.NoncompactPlaneReconstructionProof
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalFirstDiskNullCurveBridge
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.IntersectionParity.BigonDiskData
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCountableUniversalCoverHeader
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCoverDomainTransportHeader
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalSphereCoverDiskHeader
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter

namespace OriginalHalfLevelInterior
open Set Topology
open LeanEval.Topology.ClassificationOfSurfaces.Moise
set_option maxHeartbeats 0
private noncomputable def actualHalfLevelPush (P : IntrinsicTwoComplex) (s : Finset P.Vertex)
    (x : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v}) (t : unitInterval) : P.realization := by
  classical
  let a : ℝ := ∑ v ∈ s,x.val.val v
  have ha : (1 : ℝ)/2 ≤ a := x.property
  have haPos : 0 < a := by linarith
  let y : P.Vertex → ℝ := fun v => (1-(t : ℝ))*x.val.val v +
    (t : ℝ)/a*(if v ∈ s then x.val.val v else 0)
  refine ⟨y,?_,?_⟩
  · constructor
    · intro v
      dsimp [y]
      have hxv := x.val.property.1.1 v
      have hpos : 0 ≤ (if v ∈ s then x.val.val v else 0) := by split_ifs <;> positivity
      have ht0 : 0 ≤ (t : ℝ) := t.property.1
      have ht1 : (t : ℝ) ≤ 1 := t.property.2
      positivity
    · have hsum : ∑ v : P.Vertex,x.val.val v=1 := x.val.property.1.2
      have hs : (∑ v : P.Vertex,if v ∈ s then x.val.val v else 0)=a := by
        simp [a,Finset.sum_filter]
      simp only [y,Finset.sum_add_distrib,←Finset.mul_sum,hsum,hs]
      field_simp
      ring
  · obtain ⟨f,hf,hxf⟩ := x.val.property.2
    refine ⟨f,hf,?_⟩
    intro v hv
    have hz := hxf v hv
    simp [y,hz]
private theorem actualPushBound (P : IntrinsicTwoComplex) (s : Finset P.Vertex)
    (x : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v})
    (t : unitInterval) :
    (1 : ℝ)/2 ≤ ∑ v ∈ s,(actualHalfLevelPush P s x t).val v := by
  classical
  let a : ℝ := ∑ v ∈ s,x.val.val v
  have ha : (1 : ℝ)/2 ≤ a := x.property
  have haPos : 0<a := by linarith
  have hle : a ≤ 1 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun v _ _ => x.val.property.1.1 v))
    exact le_of_eq x.val.property.1.2
  have hsum : (∑ v ∈ s,(actualHalfLevelPush P s x t).val v)=
      (1-(t : ℝ))*a+(t : ℝ) := by
    simp only [actualHalfLevelPush,Finset.sum_add_distrib,←Finset.mul_sum]
    have hs : (∑ v ∈ s, if v ∈ s then x.val.val v else 0)=a := by simp [a]
    rw [hs]
    change (1-(t : ℝ))*a+((t : ℝ)/a)*a=(1-(t : ℝ))*a+(t : ℝ)
    rw [div_mul_cancel₀ _ haPos.ne']
  rw [hsum]
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hle)]
private theorem actualPushContinuous (P : IntrinsicTwoComplex) (s : Finset P.Vertex) :
    Continuous (fun p : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} × unitInterval =>
      actualHalfLevelPush P s p.1 p.2) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  change Continuous (fun p : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} × unitInterval =>
    (1-(p.2 : ℝ))*p.1.val.val v + (p.2 : ℝ)/(∑ w ∈ s,p.1.val.val w)*
      (if v ∈ s then p.1.val.val v else 0))
  have hm : Continuous (fun p : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} × unitInterval =>
      ∑ w ∈ s,p.1.val.val w) := by fun_prop
  have hne : ∀ p : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} × unitInterval,
      (∑ w ∈ s,p.1.val.val w) ≠ 0 := by
    intro p
    have h : (1 : ℝ)/2 ≤ ∑ w ∈ s,p.1.val.val w := p.1.property
    linarith
  have ht : Continuous (fun p : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} × unitInterval =>
      (p.2 : ℝ)) := by fun_prop
  have hv : Continuous (fun p : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} × unitInterval =>
      p.1.val.val v) := (continuous_apply v).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
  apply Continuous.add ((continuous_const.sub ht).mul hv)
  apply Continuous.mul (ht.div hm hne)
  split_ifs <;> fun_prop
private theorem actualPushZero (P : IntrinsicTwoComplex) (s : Finset P.Vertex)
    (x : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v}) :
    actualHalfLevelPush P s x 0=x.val := by
  apply Subtype.ext
  funext v
  simp [actualHalfLevelPush]

private noncomputable def actualHalfLevelPushWithin (P : IntrinsicTwoComplex) (s : Finset P.Vertex)
    (x : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v}) (t : unitInterval) :
    {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} :=
  ⟨actualHalfLevelPush P s x t,actualPushBound P s x t⟩
private theorem actualWithinContinuous (P : IntrinsicTwoComplex) (s : Finset P.Vertex) :
    Continuous (fun p : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} × unitInterval =>
      actualHalfLevelPushWithin P s p.1 p.2) :=
  (actualPushContinuous P s).subtype_mk _
private theorem actualComponentPush (P : IntrinsicTwoComplex) (s : Finset P.Vertex)
    (base x : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v})
    (hx : x ∈ connectedComponent base) (t : unitInterval) :
    actualHalfLevelPushWithin P s x t ∈ connectedComponent base := by
  have hc : Continuous (fun u : unitInterval => actualHalfLevelPushWithin P s x u) :=
    ((actualPushContinuous P s).comp (continuous_const.prodMk continuous_id)).subtype_mk _
  have hzero : actualHalfLevelPushWithin P s x 0=x := by
    apply Subtype.ext
    exact actualPushZero P s x
  have hs := (isConnected_range hc).isPreconnected.subset_connectedComponent
    (show x ∈ Set.range (fun u : unitInterval => actualHalfLevelPushWithin P s x u) from
      ⟨0,hzero⟩)
  rw [←connectedComponent_eq hx] at hs
  exact hs ⟨t,rfl⟩

private theorem actualPushStrict (P : IntrinsicTwoComplex) (s : Finset P.Vertex)
    (x : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v})
    (t : unitInterval) (ht : 0 < (t : ℝ)) :
    (1 : ℝ)/2 < ∑ v ∈ s,(actualHalfLevelPush P s x t).val v := by
  classical
  let a : ℝ := ∑ v ∈ s,x.val.val v
  have ha : (1 : ℝ)/2 ≤ a := x.property
  have haPos : 0<a := by linarith
  have hsum : (∑ v ∈ s,(actualHalfLevelPush P s x t).val v)=
      (1-(t : ℝ))*a+(t : ℝ) := by
    simp only [actualHalfLevelPush,Finset.sum_add_distrib,←Finset.mul_sum]
    have hs : (∑ v ∈ s, if v ∈ s then x.val.val v else 0)=a := by simp [a]
    rw [hs]
    change (1-(t : ℝ))*a+((t : ℝ)/a)*a=(1-(t : ℝ))*a+(t : ℝ)
    rw [div_mul_cancel₀ _ haPos.ne']
  rw [hsum]
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha)]
private theorem actualStrictComponentConnected (P : IntrinsicTwoComplex) (s : Finset P.Vertex)
    (base : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v}) :
    IsConnected {x : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} |
      x ∈ connectedComponent base ∧ (1 : ℝ)/2 < ∑ v ∈ s,x.val.val v} := by
  classical
  let N := {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v}
  let C : Set N := connectedComponent base
  letI : ConnectedSpace C := Subtype.connectedSpace isConnected_connectedComponent
  let q : C × unitInterval → N := fun p => actualHalfLevelPushWithin P s p.1.val p.2
  have hq : Continuous q := (actualWithinContinuous P s).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let W : Set (C × unitInterval) := Set.univ ×ˢ Set.Ioi (0 : unitInterval)
  have htime : IsConnected (Set.Ioi (0 : unitInterval)) :=
    ⟨⟨1,by norm_num⟩,isPreconnected_Ioi⟩
  have hW : IsConnected W := isConnected_univ.prod htime
  have hImage : IsConnected (q '' W) := hW.image q hq.continuousOn
  have hSub : q '' W ⊆ {x : N | x ∈ C ∧ (1 : ℝ)/2 < ∑ v ∈ s,x.val.val v} := by
    rintro x ⟨⟨c,t⟩,ht,rfl⟩
    exact ⟨actualComponentPush P s base c.val c.property t,actualPushStrict P s c.val t ht.2⟩
  have hClosure : C ⊆ closure (q '' W) := by
    intro x hx
    have ht0 : (0 : unitInterval) ∈ closure (Set.Ioi (0 : unitInterval)) := by
      rw [closure_Ioi' ⟨1,by norm_num⟩]
      exact show (0 : unitInterval) ≤ 0 from le_rfl
    have hp : (⟨x,hx⟩,0) ∈ closure W := by
      rw [closure_prod_eq]
      exact ⟨subset_closure (Set.mem_univ _),ht0⟩
    have h := mem_closure_image hq.continuousAt hp
    have heq : q (⟨x,hx⟩,0)=x := by
      apply Subtype.ext
      exact actualPushZero P s x
    rw [heq] at h
    exact h
  exact hImage.subset_closure hSub (fun x hx => hClosure hx.1)

private theorem actualStrictComponentClosure (P : IntrinsicTwoComplex) (s : Finset P.Vertex)
    (base : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v}) :
    closure {x : {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v} |
      x ∈ connectedComponent base ∧ (1 : ℝ)/2 < ∑ v ∈ s,x.val.val v} = connectedComponent base := by
  classical
  let N := {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ s,x.val v}
  let C : Set N := connectedComponent base
  letI : ConnectedSpace C := Subtype.connectedSpace isConnected_connectedComponent
  let q : C × unitInterval → N := fun p => actualHalfLevelPushWithin P s p.1.val p.2
  have hq : Continuous q := (actualWithinContinuous P s).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let W : Set (C × unitInterval) := Set.univ ×ˢ Set.Ioi (0 : unitInterval)
  have htime : IsConnected (Set.Ioi (0 : unitInterval)) :=
    ⟨⟨1,by norm_num⟩,isPreconnected_Ioi⟩
  have hW : IsConnected W := isConnected_univ.prod htime
  have hImage : IsConnected (q '' W) := hW.image q hq.continuousOn
  have hSub : q '' W ⊆ {x : N | x ∈ C ∧ (1 : ℝ)/2 < ∑ v ∈ s,x.val.val v} := by
    rintro x ⟨⟨c,t⟩,ht,rfl⟩
    exact ⟨actualComponentPush P s base c.val c.property t,actualPushStrict P s c.val t ht.2⟩
  have hClosure : C ⊆ closure (q '' W) := by
    intro x hx
    have ht0 : (0 : unitInterval) ∈ closure (Set.Ioi (0 : unitInterval)) := by
      rw [closure_Ioi' ⟨1,by norm_num⟩]
      exact show (0 : unitInterval) ≤ 0 from le_rfl
    have hp : (⟨x,hx⟩,0) ∈ closure W := by
      rw [closure_prod_eq]
      exact ⟨subset_closure (Set.mem_univ _),ht0⟩
    have h := mem_closure_image hq.continuousAt hp
    have heq : q (⟨x,hx⟩,0)=x := by
      apply Subtype.ext
      exact actualPushZero P s x
    rw [heq] at h
    exact h
  apply Set.Subset.antisymm
  · exact closure_minimal (fun x hx => hx.1) isClosed_connectedComponent
  · exact hClosure.trans (closure_mono hSub)



end OriginalHalfLevelInterior

namespace OriginalBoundaryGeometry
open Set Topology
set_option maxHeartbeats 0
private theorem actualWalkTraceComponent {V X : Type} [TopologicalSpace X]
    (G : SimpleGraph V) (position : V → X)
    (hposition : Function.Injective position)
    (arc : ∀ {u v}, G.Adj u v → Path (position u) (position v))
    (trace : ∀ {u v}, G.Walk u v → Set X)
    (hnil : ∀ u, trace (SimpleGraph.Walk.nil : G.Walk u u)={position u})
    (hcons : ∀ {u v w} (h : G.Adj u v) (p : G.Walk v w),
      trace (.cons h p)=Set.range (arc h) ∪ trace p)
    (hvertex : ∀ {u v} (h : G.Adj u v) x, position x ∈ Set.range (arc h) → x=u ∨ x=v) :
    ∀ {u v} (p : G.Walk u v) x, position x ∈ trace p → G.Reachable u x := by
  intro u v p
  induction p with
  | @nil u =>
    intro x hx
    rw [hnil,Set.mem_singleton_iff] at hx
    have hxu : x=u := hposition hx
    subst x
    exact .refl _
  | @cons u v w h p ih =>
    intro x hx
    rw [hcons] at hx
    rcases hx with hx | hx
    · rcases hvertex h x hx with rfl | rfl
      · exact .refl _
      · exact h.reachable
    · exact h.reachable.trans (ih x hx)

private theorem actualWalkTraceArcComponent {V X : Type} [TopologicalSpace X]
    (G : SimpleGraph V) (position : V → X) (hposition : Function.Injective position)
    (arc : ∀ {u v}, G.Adj u v → Path (position u) (position v))
    (trace : ∀ {u v}, G.Walk u v → Set X)
    (hnil : ∀ u, trace (SimpleGraph.Walk.nil : G.Walk u u)={position u})
    (hcons : ∀ {u v w} (h : G.Adj u v) (p : G.Walk v w),
      trace (.cons h p)=Set.range (arc h) ∪ trace p)
    (hvertex : ∀ {u v} (h : G.Adj u v) x, position x ∈ Set.range (arc h) → x=u ∨ x=v)
    (hmeet : ∀ {u v w z} (h : G.Adj u v) (k : G.Adj w z),
      (Set.range (arc h) ∩ Set.range (arc k)).Nonempty → G.Reachable u w) :
    ∀ {u v w z} (p : G.Walk u v) (h : G.Adj w z),
      (trace p ∩ Set.range (arc h)).Nonempty → G.Reachable u w := by
  intro u v w z p
  induction p with
  | @nil u =>
    intro h ⟨x,hx,hxa⟩
    rw [hnil,Set.mem_singleton_iff] at hx
    rw [hx] at hxa
    rcases hvertex h u hxa with rfl | rfl
    · exact .refl _
    · exact h.symm.reachable
  | @cons u v y h p ih =>
    intro k ⟨x,hx,hxa⟩
    rw [hcons] at hx
    rcases hx with hx | hx
    · exact hmeet h k ⟨x,hx,hxa⟩
    · exact h.reachable.trans (ih k ⟨x,hx,hxa⟩)
private theorem actualWalkTracesMeetComponent {V X : Type} [TopologicalSpace X]
    (G : SimpleGraph V) (position : V → X) (hposition : Function.Injective position)
    (arc : ∀ {u v}, G.Adj u v → Path (position u) (position v))
    (trace : ∀ {u v}, G.Walk u v → Set X)
    (hnil : ∀ u, trace (SimpleGraph.Walk.nil : G.Walk u u)={position u})
    (hcons : ∀ {u v w} (h : G.Adj u v) (p : G.Walk v w),
      trace (.cons h p)=Set.range (arc h) ∪ trace p)
    (hvertex : ∀ {u v} (h : G.Adj u v) x, position x ∈ Set.range (arc h) → x=u ∨ x=v)
    (hmeet : ∀ {u v w z} (h : G.Adj u v) (k : G.Adj w z),
      (Set.range (arc h) ∩ Set.range (arc k)).Nonempty → G.Reachable u w) :
    ∀ {u v w z} (p : G.Walk u v) (q : G.Walk w z),
      (trace p ∩ trace q).Nonempty → G.Reachable u w := by
  intro u v w z p q
  induction q with
  | @nil w =>
    rintro ⟨x,hxp,hxq⟩
    rw [hnil,Set.mem_singleton_iff] at hxq
    rw [hxq] at hxp
    exact actualWalkTraceComponent G position hposition arc trace hnil hcons hvertex p w hxp
  | @cons w z y k q ih =>
    rintro ⟨x,hxp,hxq⟩
    rw [hcons] at hxq
    rcases hxq with hxq | hxq
    · exact actualWalkTraceArcComponent G position hposition arc trace hnil hcons hvertex hmeet p k ⟨x,hxp,hxq⟩
    · exact (ih ⟨x,hxp,hxq⟩).trans k.symm.reachable
open Set Topology
set_option maxHeartbeats 0
private theorem actualTraceCoversWalkEdges {V X : Type} [TopologicalSpace X]
    (G : SimpleGraph V) (position : V → X)
    (arc : ∀ {u v}, G.Adj u v → Path (position u) (position v))
    (trace : ∀ {u v}, G.Walk u v → Set X)
    (hcons : ∀ {u v w} (h : G.Adj u v) (p : G.Walk v w),
      trace (.cons h p)=Set.range (arc h) ∪ trace p)
    (hrev : ∀ {u v} (h : G.Adj u v), Set.range (arc h.symm)=Set.range (arc h)) :
    ∀ {u v} (p : G.Walk u v) {w z} (h : G.Adj w z),
      p.toSubgraph.Adj w z → Set.range (arc h) ⊆ trace p := by
  intro u v p
  induction p with
  | nil =>
    intro w z h hp
    simpa using hp
  | @cons u v y k p ih =>
    intro w z h hp
    rw [SimpleGraph.Walk.toSubgraph,SimpleGraph.Subgraph.sup_adj] at hp
    rw [hcons]
    rcases hp with hp | hp
    · rw [SimpleGraph.subgraphOfAdj_adj] at hp
      rw [Sym2.eq_iff] at hp
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Set.subset_union_left
      · rw [hrev k]
        exact Set.subset_union_left
    · exact (ih h hp).trans Set.subset_union_right

private theorem actualCycleTraceCoversComponentEdges {V X : Type} [Finite V] [TopologicalSpace X]
    (G : SimpleGraph V) (position : V → X)
    (arc : ∀ {u v}, G.Adj u v → Path (position u) (position v))
    (trace : ∀ {u v}, G.Walk u v → Set X)
    (hcons : ∀ {u v w} (h : G.Adj u v) (p : G.Walk v w),
      trace (.cons h p)=Set.range (arc h) ∪ trace p)
    (hrev : ∀ {u v} (h : G.Adj u v), Set.range (arc h.symm)=Set.range (arc h))
    (hdegree : ∀ u, (G.neighborSet u).ncard=2)
    {u : V} (p : G.Walk u u) (hp : p.IsCycle)
    (hcomp : p.toSubgraph.verts=(G.connectedComponentMk u).supp)
    {w z : V} (h : G.Adj w z) (hw : G.Reachable u w) :
    Set.range (arc h) ⊆ trace p := by
  have hmem : w ∈ p.toSubgraph.verts := by
    rw [hcomp,SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound hw.symm
  have hsupport : w ∈ p.support := by
    exact p.mem_verts_toSubgraph.mp hmem
  have hNeighbors : p.toSubgraph.neighborSet w=G.neighborSet w := by
    apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset w)
    rw [hdegree,hp.ncard_neighborSet_toSubgraph_eq_two hsupport]
  have hadj : p.toSubgraph.Adj w z := by
    change z ∈ p.toSubgraph.neighborSet w
    rw [hNeighbors]
    exact h
  exact actualTraceCoversWalkEdges G position arc trace hcons hrev p h hadj
open Set
set_option maxHeartbeats 0
private theorem actualCutFaceUnique {V : Type} [DecidableEq V]
    (u v f g : Finset V) (hu : u.card=2) (hv : v.card=2) (hne : u ≠ v)
    (hf : f.card=3) (hg : g.card=3)
    (huf : u ⊆ f) (hvf : v ⊆ f) (hug : u ⊆ g) (hvg : v ⊆ g) : f=g := by
  have hcard : 3 ≤ (u ∪ v).card := by
    by_contra hc
    have hle : (u ∪ v).card ≤ 2 := by omega
    have he : u=u ∪ v := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have hvu : v ⊆ u := he ▸ Finset.subset_union_right
    exact hne (Finset.eq_of_subset_of_card_le hvu (by omega)).symm
  have hfEq : u ∪ v=f := Finset.eq_of_subset_of_card_le
    (Finset.union_subset huf hvf) (by omega)
  have hgEq : u ∪ v=g := Finset.eq_of_subset_of_card_le
    (Finset.union_subset hug hvg) (by omega)
  exact hfEq.symm.trans hgEq
end OriginalBoundaryGeometry

namespace OriginalPartialPlaneEngulfing

open Set Topology Metric
open ClassificationJordanCurve.Arcs
set_option maxHeartbeats 0
private theorem actualUnitSphereJordan : Schoenflies.IsJordanCurve (sphere (0 : Plane) 1) := by
  let r : C(Circle, Plane) := ⟨fun z => (circleHomeoSphere z : Plane),
    continuous_subtype_val.comp circleHomeoSphere.continuous⟩
  have hr : Topology.IsEmbedding r := Topology.IsEmbedding.subtypeVal.comp circleHomeoSphere.isEmbedding
  have hrange : Set.range r=sphere (0 : Plane) 1 := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact (circleHomeoSphere z).property
    · intro hx
      refine ⟨circleHomeoSphere.symm ⟨x,hx⟩,?_⟩
      change (circleHomeoSphere (circleHomeoSphere.symm ⟨x,hx⟩) : Plane)=x
      rw [circleHomeoSphere.apply_symm_apply]
  rw [←hrange]
  exact CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr
private theorem actualUnitSphereInside : Schoenflies.inside (sphere (0 : Plane) 1)=ball (0 : Plane) 1 := by
  have hsub : ball (0 : Plane) 1 ⊆ (sphere (0 : Plane) 1)ᶜ := by
    intro x hx hs
    exact (ne_of_lt (mem_ball.mp hx)) (mem_sphere.mp hs)
  have hfr : frontier (ball (0 : Plane) 1) ∩ (sphere (0 : Plane) 1)ᶜ=∅ := by
    rw [frontier_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
    exact Set.inter_compl_self _
  have hzero : (0 : Plane) ∈ ball (0 : Plane) 1 := by simp
  have hcomp := Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint
    Metric.isOpen_ball (convex_ball (0 : Plane) 1).isPreconnected hsub hfr hzero
  have hinside : (0 : Plane) ∈ Schoenflies.inside (sphere (0 : Plane) 1) := by
    refine ⟨hsub hzero,?_⟩
    rw [hcomp]
    exact Metric.isBounded_ball
  exact ((Schoenflies.jordan_curve_theorem actualUnitSphereJordan).connectedComponentIn_eq_inside hinside).symm.trans hcomp
private theorem actualUnitSphereOutside : Schoenflies.outside (sphere (0 : Plane) 1)={x : Plane | 1<‖x‖} := by
  ext x
  have hUnion := Schoenflies.inside_union_outside (sphere (0 : Plane) 1)
  have hDisj := Schoenflies.disjoint_inside_outside (C := sphere (0 : Plane) 1)
  rw [actualUnitSphereInside] at hUnion hDisj
  constructor
  · intro hx
    have hnotBall : x ∉ ball (0 : Plane) 1 := fun hb => Set.disjoint_left.mp hDisj hb hx
    have hnotSphere := Schoenflies.outside_subset_compl hx
    have hle : 1 ≤ ‖x‖ := by simpa [mem_ball,dist_zero_right] using hnotBall
    exact lt_of_le_of_ne hle (fun h => hnotSphere (mem_sphere_zero_iff_norm.mpr h.symm))
  · intro hx
    have hnotSphere : x ∈ (sphere (0 : Plane) 1)ᶜ := by
      intro hs
      have hn := mem_sphere_zero_iff_norm.mp hs
      exact (ne_of_gt hx) hn
    have h := hUnion.symm ▸ hnotSphere
    rcases h with hb | ho
    · have hn : ‖x‖<1 := by simpa only [mem_ball,dist_zero_right] using hb
      exact False.elim (not_lt_of_gt hx hn)
    · exact ho
private theorem actualOutsideHomeomorphIff (F : Plane ≃ₜ Plane) (C : Set Plane) (x : Plane) :
    x ∈ Schoenflies.outside C ↔ F x ∈ Schoenflies.outside (F '' C) := by
  classical
  have hC : F x ∈ F '' C ↔ x ∈ C := by
    constructor
    · rintro ⟨y,hy,he⟩; exact F.injective he ▸ hy
    · intro hx; exact ⟨x,hx,rfl⟩
  have hI : F x ∈ Schoenflies.inside (F '' C) ↔ x ∈ Schoenflies.inside C := by
    rw [←CurveComplex.jordan_inside_homeomorph_image]
    constructor
    · rintro ⟨y,hy,he⟩; exact F.injective he ▸ hy
    · intro hx; exact ⟨x,hx,rfl⟩
  constructor
  · intro hx
    refine ⟨fun h => hx.1 (hC.mp h),?_⟩
    intro hb
    exact hx.2 (hI.mp ⟨fun h => hx.1 (hC.mp h),hb⟩).2
  · intro hx
    refine ⟨fun h => hx.1 (hC.mpr h),?_⟩
    intro hb
    exact hx.2 (hI.mpr ⟨fun h => hx.1 (hC.mpr h),hb⟩).2
open Set Topology Metric
open ClassificationJordanCurve.Arcs
set_option maxHeartbeats 0
private theorem actualOuterAnnulusConnected (R : ℝ) (hR : 1<R) :
    IsConnected {x : Plane | 1<‖x‖ ∧ ‖x‖<R} := by
  let I := Set.Ioo (1 : ℝ) R
  letI : ConnectedSpace I := Subtype.connectedSpace (isConnected_Ioo hR)
  let f : Circle × I → Plane := fun p => (p.2.val : ℝ) • (circleHomeoSphere p.1).val
  have hf : Continuous f := by fun_prop
  have heq : Set.range f={x : Plane | 1<‖x‖ ∧ ‖x‖<R} := by
    ext x
    constructor
    · rintro ⟨⟨z,t⟩,rfl⟩
      have hz : ‖(circleHomeoSphere z).val‖=1 := mem_sphere_zero_iff_norm.mp (circleHomeoSphere z).property
      have htpos : 0<t.val := lt_trans zero_lt_one t.property.1
      simpa only [I,Set.mem_Ioo,Set.mem_setOf_eq,f,norm_smul,Real.norm_eq_abs,abs_of_pos htpos,hz,mul_one] using t.property
    · intro hx
      have hn : 0<‖x‖ := lt_trans zero_lt_one hx.1
      let u : sphere (0 : Plane) 1 := ⟨‖x‖⁻¹ • x, by
        rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hn.ne']⟩
      refine ⟨⟨circleHomeoSphere.symm u,⟨‖x‖,hx⟩⟩,?_⟩
      change ‖x‖ • (circleHomeoSphere (circleHomeoSphere.symm u)).val=x
      rw [circleHomeoSphere.apply_symm_apply]
      change ‖x‖ • (‖x‖⁻¹ • x)=x
      rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  rw [←heq]
  exact isConnected_range hf

private theorem actualUnitSphereClosureOuterAnnulus (R : ℝ) (hR : 1<R) :
    sphere (0 : Plane) 1 ⊆ closure {x : Plane | 1<‖x‖ ∧ ‖x‖<R} := by
  intro x hx
  have hn : ‖x‖=1 := mem_sphere_zero_iff_norm.mp hx
  have htime : (1 : ℝ) ∈ closure (Set.Ioo 1 R) := by
    rw [closure_Ioo hR.ne]
    exact ⟨le_rfl,hR.le⟩
  have hlim := mem_closure_image
    (show ContinuousAt (fun t : ℝ => t • x) 1 from (continuous_id.smul continuous_const).continuousAt) htime
  have hsub : (fun t : ℝ => t • x) '' Set.Ioo 1 R ⊆ {y : Plane | 1<‖y‖ ∧ ‖y‖<R} := by
    rintro y ⟨t,ht,rfl⟩
    have htpos : 0<t := lt_trans zero_lt_one ht.1
    simpa only [Set.mem_Ioo,Set.mem_setOf_eq,norm_smul,Real.norm_eq_abs,abs_of_pos htpos,hn,mul_one] using ht
  have h := closure_mono hsub hlim
  simpa only [one_smul] using h
private theorem actualOpenUnitSphereNeighborhoodContainsOuterAnnulus
    (V : Set Plane) (hV : IsOpen V) (hSphere : sphere (0 : Plane) 1 ⊆ V) :
    ∃ R : ℝ, 1<R ∧ {x : Plane | 1<‖x‖ ∧ ‖x‖<R} ⊆ V := by
  obtain ⟨ε,hε,hThick⟩ := (isCompact_sphere (0 : Plane) 1).exists_cthickening_subset_open hV hSphere
  refine ⟨1+ε,by linarith,?_⟩
  intro x hx
  have hn : 0<‖x‖ := lt_trans zero_lt_one hx.1
  let y : Plane := ‖x‖⁻¹ • x
  have hy : y ∈ sphere (0 : Plane) 1 := by
    rw [mem_sphere_zero_iff_norm]
    dsimp [y]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hn.ne']
  apply hThick
  apply Metric.mem_cthickening_of_dist_le x y ε _ hy
  have hd : dist x y=‖x‖-1 := by
    rw [dist_eq_norm]
    change ‖x-‖x‖⁻¹ • x‖=‖x‖-1
    have he : x-‖x‖⁻¹ • x=(1-‖x‖⁻¹) • x := by rw [sub_smul,one_smul]
    rw [he,norm_smul,Real.norm_eq_abs]
    have hi : ‖x‖⁻¹<1 := inv_lt_one_of_one_lt₀ hx.1
    rw [abs_of_pos (by linarith : 0<1-‖x‖⁻¹)]
    field_simp [hn.ne']
  rw [hd]
  linarith [hx.2]

private theorem actualIsolatedSphereExteriorInteriorCollar
    (A V : Set Plane) (hA : IsClosed A) (hRegular : closure (interior A)=A)
    (hSphere : sphere (0 : Plane) 1 ⊆ frontier A)
    (hV : IsOpen V) (hSV : sphere (0 : Plane) 1 ⊆ V)
    (hFront : ∀ x ∈ V, x ∈ frontier A ↔ x ∈ sphere (0 : Plane) 1)
    (hOutside : interior A ⊆ {x : Plane | 1<‖x‖}) :
    ∃ R : ℝ, 1<R ∧ {x : Plane | 1<‖x‖ ∧ ‖x‖<R} ⊆ interior A := by
  obtain ⟨R,hR,hRV⟩ := actualOpenUnitSphereNeighborhoodContainsOuterAnnulus V hV hSV
  let B : Set Plane := {x | 1<‖x‖ ∧ ‖x‖<R}
  have hB : IsConnected B := actualOuterAnnulusConnected R hR
  have hCover : B ⊆ interior A ∪ Aᶜ := by
    intro x hx
    by_cases hxA : x ∈ A
    · left
      by_contra hxInt
      have hfr : x ∈ frontier A := by rw [frontier,hA.closure_eq]; exact ⟨hxA,hxInt⟩
      have hs := (hFront x (hRV hx)).mp hfr
      have hnorm := mem_sphere_zero_iff_norm.mp hs
      have hlt := hx.1
      linarith
    · exact Or.inr hxA
  let x : Plane := (circleHomeoSphere (1 : Circle)).val
  have hxS : x ∈ sphere (0 : Plane) 1 := (circleHomeoSphere 1).property
  have hxA : x ∈ A := hA.frontier_subset (hSphere hxS)
  have hxClosure : x ∈ closure (interior A) := hRegular.symm ▸ hxA
  have hOpen : IsOpen {y : Plane | ‖y‖<R} := isOpen_lt continuous_norm continuous_const
  have hxNorm : ‖x‖<R := by rw [mem_sphere_zero_iff_norm.mp hxS]; exact hR
  have hnear : x ∈ closure ({y : Plane | ‖y‖<R} ∩ interior A) :=
    hOpen.inter_closure ⟨hxNorm,hxClosure⟩
  obtain ⟨y,hyNorm,hyA⟩ := Set.Nonempty.of_closure ⟨x,hnear⟩
  have hyB : y ∈ B := ⟨hOutside hyA,hyNorm⟩
  refine ⟨R,hR,?_⟩
  rcases hB.isPreconnected.subset_or_subset isOpen_interior hA.isOpen_compl
    (Set.disjoint_left.mpr (fun z hz hzC => hzC (interior_subset hz))) hCover with hIn | hOut
  · exact hIn
  · exact False.elim ((hOut hyB) (interior_subset hyA))
open Set Topology Bornology
set_option maxHeartbeats 0
private theorem actualExtremeRightRayOutside (C : Set Schoenflies.Plane)
    (z : Schoenflies.Plane) (hmax : ∀ x ∈ C, x 0 ≤ z 0)
    (t : ℝ) (ht : 0<t) :
    z+t • WithLp.toLp 2 (fun i : Fin 2 => if i=0 then (1 : ℝ) else 0) ∈ Schoenflies.outside C := by
  let e : Schoenflies.Plane := WithLp.toLp 2 (fun i : Fin 2 => if i=0 then (1 : ℝ) else 0)
  let q : ℝ → Schoenflies.Plane := fun s => z+s • e
  have hq : Continuous q := by fun_prop
  have hcoord (s : ℝ) : q s 0=z 0+s := by simp [q,e]
  let ray := q '' Set.Ici t
  have hConnected : IsPreconnected ray := isPreconnected_Ici.image q hq.continuousOn
  have hOff : ray ⊆ Cᶜ := by
    rintro x ⟨s,hs,rfl⟩ hx
    have hb := hmax (q s) hx
    rw [hcoord] at hb
    change t ≤ s at hs
    linarith
  have hpoint : q t ∈ ray := ⟨t,Set.self_mem_Ici,rfl⟩
  have hSub := hConnected.subset_connectedComponentIn hpoint hOff
  refine ⟨hOff hpoint,?_⟩
  intro hb
  have hRayBound : IsBounded ray := hb.subset hSub
  have hcoordBound : IsBounded ((fun x : Schoenflies.Plane => x 0) '' ray) :=
    ((hRayBound.isCompact_closure.image (by fun_prop : Continuous (fun x : Schoenflies.Plane => x 0))).isBounded).subset
      (Set.image_mono subset_closure)
  obtain ⟨R,hR⟩ := hcoordBound.exists_norm_le
  let s := max t (R-z 0+1)
  have hs : t ≤ s := le_max_left _ _
  have hs' : R-z 0+1 ≤ s := le_max_right _ _
  have h := hR (q s 0) ⟨q s,⟨s,hs,rfl⟩,rfl⟩
  rw [hcoord,Real.norm_eq_abs] at h
  have := le_abs_self (z 0+s)
  linarith
open Set Topology
set_option maxHeartbeats 0
private theorem actualConnectedInteriorJordanSide
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : IsConnected (interior A)) (hRegular : closure (interior A)=A)
    (c : CurveComplex.Curve (EuclideanSpace ℝ (Fin 2)))
    (hc : c.image ⊆ frontier A) :
    (interior A ⊆ Schoenflies.inside c.image ∧ A ⊆ closure (Schoenflies.inside c.image)) ∨
    (interior A ⊆ Schoenflies.outside c.image ∧ A ⊆ closure (Schoenflies.outside c.image)) := by
  have hJ := CurveComplex.isJordanCurve_range_of_isEmbedding_circle
    (⟨c.map,c.embedded.continuous⟩ : C(Circle,EuclideanSpace ℝ (Fin 2))) c.embedded
  have hS := Schoenflies.jordan_curve_theorem hJ
  have hCover : interior A ⊆ Schoenflies.inside c.image ∪ Schoenflies.outside c.image := by
    rw [Schoenflies.inside_union_outside]
    intro x hx hxc
    exact (hc hxc).2 hx
  rcases hA.isPreconnected.subset_or_subset hS.isOpen_inside hS.isOpen_outside
    Schoenflies.disjoint_inside_outside hCover with hIn | hOut
  · exact Or.inl ⟨hIn,hRegular ▸ closure_mono hIn⟩
  · exact Or.inr ⟨hOut,hRegular ▸ closure_mono hOut⟩
open ClassificationJordanCurve.Arcs CurveComplex
private theorem actualNormalize (c : Curve Plane) : ∃ F : Plane ≃ₜ Plane,
    ∀ z : Circle, F (c.map z) = complexLIE z := by
  let r : C(Circle, Plane) := ⟨fun z => (circleHomeoSphere z : Plane),
    continuous_subtype_val.comp circleHomeoSphere.continuous⟩
  have hr : Topology.IsEmbedding r :=
    Topology.IsEmbedding.subtypeVal.comp circleHomeoSphere.isEmbedding
  have hrange : Set.range r = sphere (0 : Plane) 1 := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact (circleHomeoSphere z).property
    · intro hx
      refine ⟨circleHomeoSphere.symm ⟨x,hx⟩,?_⟩
      change (circleHomeoSphere (circleHomeoSphere.symm ⟨x,hx⟩) : Plane)=x
      rw [circleHomeoSphere.apply_symm_apply]
  have hJ := isJordanCurve_range_of_isEmbedding_circle r hr
  rw [hrange] at hJ
  -- the range homeomorphism has the opposite direction here
  let ec : c.image ≃ₜ sphere (0 : Plane) 1 := c.embedded.toHomeomorph.symm.trans circleHomeoSphere
  obtain ⟨F,hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    (isJordanCurve_range_of_isEmbedding_circle ⟨c.map,c.embedded.continuous⟩ c.embedded) hJ ec
  refine ⟨F,fun z => ?_⟩
  have h := hF ⟨c.map z,⟨z,rfl⟩⟩
  simpa [ec] using h


private theorem actualIsolatedExtremeBoundaryEngulfs
    (A : Set Plane) (hA : IsClosed A) (hRegular : closure (interior A)=A)
    (hConnected : IsConnected (interior A))
    (c : CurveComplex.Curve Plane) (hc : c.image ⊆ frontier A)
    (V : Set Plane) (hV : IsOpen V) (hCV : c.image ⊆ V)
    (hFront : ∀ x ∈ V, x ∈ frontier A ↔ x ∈ c.image)
    (z : Plane) (hz : z ∈ c.image) (hMax : ∀ x ∈ A, x 0 ≤ z 0) :
    A ⊆ Schoenflies.inside c.image ∪ c.image := by
  classical
  have hJ : Schoenflies.IsJordanCurve c.image := CurveComplex.isJordanCurve_range_of_isEmbedding_circle
    (⟨c.map,c.embedded.continuous⟩ : C(Circle,Plane)) c.embedded
  have hS := Schoenflies.jordan_curve_theorem hJ
  rcases actualConnectedInteriorJordanSide A hConnected hRegular c hc with hIn | hOut
  · rw [closure_eq_self_union_frontier,hS.frontier_inside] at hIn
    exact hIn.2
  · obtain ⟨F,hF⟩ := actualNormalize c
    have hImage : F '' c.image=sphere (0 : Plane) 1 := by
      ext q
      constructor
      · rintro ⟨w,⟨t,rfl⟩,rfl⟩
        rw [hF]; exact (circleHomeoSphere t).property
      · intro hq
        refine ⟨c.map (circleHomeoSphere.symm ⟨q,hq⟩),⟨_,rfl⟩,?_⟩
        rw [hF]
        exact congrArg Subtype.val (circleHomeoSphere.apply_symm_apply ⟨q,hq⟩)
    have hFA : IsClosed (F '' A) := F.isClosedMap _ hA
    have hFRegular : closure (interior (F '' A))=F '' A := by
      rw [←F.image_interior,←F.image_closure,hRegular]
    have hSphere : sphere (0 : Plane) 1 ⊆ frontier (F '' A) := by
      rw [←hImage,←F.image_frontier]
      exact Set.image_mono hc
    have hFV : IsOpen (F '' V) := F.isOpenMap _ hV
    have hSphereV : sphere (0 : Plane) 1 ⊆ F '' V := by
      rw [←hImage]
      exact Set.image_mono hCV
    have hFFront : ∀ x ∈ F '' V, x ∈ frontier (F '' A) ↔ x ∈ sphere (0 : Plane) 1 := by
      rintro x ⟨y,hy,rfl⟩
      rw [←F.image_frontier,←hImage]
      constructor
      · rintro ⟨w,hw,he⟩
        have hwy : w=y := F.injective he
        subst w
        exact ⟨y,(hFront y hy).mp hw,rfl⟩
      · rintro ⟨w,hw,he⟩
        have hwy : w=y := F.injective he
        subst w
        exact ⟨y,(hFront y hy).mpr hw,rfl⟩
    have hFOutside : interior (F '' A) ⊆ {x : Plane | 1<‖x‖} := by
      rw [←F.image_interior]
      rintro x ⟨y,hy,rfl⟩
      have ho := (actualOutsideHomeomorphIff F c.image y).mp (hOut.1 hy)
      rw [hImage,actualUnitSphereOutside] at ho
      exact ho
    obtain ⟨R,hR,hCollar⟩ := actualIsolatedSphereExteriorInteriorCollar
      (F '' A) (F '' V) hFA hFRegular hSphere hFV hSphereV hFFront hFOutside
    let e : Plane := WithLp.toLp 2 (fun i : Fin 2 => if i=0 then (1 : ℝ) else 0)
    let q : ℝ → Plane := fun t => z+t • e
    have hq : Continuous q := by fun_prop
    have hFzNorm : ‖F z‖=1 := by
      have hs : F z ∈ sphere (0 : Plane) 1 := hImage ▸ Set.mem_image_of_mem F hz
      exact mem_sphere_zero_iff_norm.mp hs
    have hopen : IsOpen {t : ℝ | ‖F (q t)‖<R} :=
      isOpen_lt (continuous_norm.comp (F.continuous.comp hq)) continuous_const
    have hzero : (0 : ℝ) ∈ {t : ℝ | ‖F (q t)‖<R} := by
      change ‖F (z+(0 : ℝ) • e)‖<R
      simpa only [zero_smul,add_zero,hFzNorm] using hR
    obtain ⟨δ,hδ,hBall⟩ := Metric.isOpen_iff.mp hopen 0 hzero
    let t : ℝ := δ/2
    have ht : 0<t := by dsimp [t]; linarith
    have htBall : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
      dsimp [t]; linarith
    have hNormUpper : ‖F (q t)‖<R := hBall htBall
    have hMaxC : ∀ x ∈ c.image, x 0 ≤ z 0 := fun x hx => hMax x (hA.frontier_subset (hc hx))
    have hRay := actualExtremeRightRayOutside c.image z hMaxC t ht
    have hFOut := (actualOutsideHomeomorphIff F c.image (q t)).mp hRay
    rw [hImage,actualUnitSphereOutside] at hFOut
    have hInFA : F (q t) ∈ F '' A := interior_subset (hCollar ⟨hFOut,hNormUpper⟩)
    obtain ⟨w,hw,he⟩ := hInFA
    have hwt : w=q t := F.injective he
    have hBound := hMax (q t) (hwt ▸ hw)
    have hqzero : q t 0=z 0+t := by simp [q,e]
    rw [hqzero] at hBound
    linarith
open Set Topology Metric
set_option maxHeartbeats 0
private theorem actualCompactExtremeFrontier
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ z ∈ frontier A, ∀ x ∈ A, x 0 ≤ z 0 := by
  obtain ⟨z,hz,hmax⟩ := hA.exists_isMaxOn hne (by fun_prop :
    ContinuousOn (fun x : EuclideanSpace ℝ (Fin 2) => x 0) A)
  refine ⟨z,⟨subset_closure hz,?_⟩,hmax⟩
  intro hzInt
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzInt
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i => if i=0 then r/2 else 0)
  have hvnorm : ‖v‖=r/2 := by
    rw [EuclideanSpace.norm_eq]
    simp [v,Fin.sum_univ_two]
    rw [Real.sqrt_sq (by positivity)]
  have hyball : z+v ∈ ball z r := by
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,hvnorm]
    linarith
  have hyA := interior_subset (hball hyball)
  have hbound := hmax hyA
  change z 0+(r/2) ≤ z 0 at hbound
  linarith

open Set Topology
set_option maxHeartbeats 0
private theorem actualCompactPartialChartRegionTransport
    {U : Type} [TopologicalSpace U] [T2Space U]
    (e : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin 2)))
    (N : Set U) (hN : IsCompact N) (hNs : N ⊆ e.source)
    (hConnected : IsConnected (interior N)) (hRegular : closure (interior N)=N) :
    IsCompact (e '' N) ∧ IsConnected (interior (e '' N)) ∧
      closure (interior (e '' N))=e '' N ∧
      e '' interior N=interior (e '' N) ∧
      ∀ x ∈ e.source, e x ∈ frontier (e '' N) ↔ x ∈ frontier N := by
  have hImage : e.IsImage N (e '' N) := by
    intro x hx
    constructor
    · rintro ⟨y,hy,he⟩
      exact e.injOn (hNs hy) hx he ▸ hy
    · intro hxN
      exact ⟨x,hxN,rfl⟩
  have hCompact := hN.image_of_continuousOn (e.continuousOn.mono hNs)
  have hTarget : e '' N ⊆ e.target := by
    rintro y ⟨x,hx,rfl⟩
    exact e.map_source (hNs hx)
  have hIntSource : interior N ⊆ e.source := interior_subset.trans hNs
  have hIntTarget : interior (e '' N) ⊆ e.target := interior_subset.trans hTarget
  have hIntImage : e '' interior N=interior (e '' N) := by
    have h := hImage.interior.image_eq
    rw [Set.inter_eq_right.mpr hIntSource,Set.inter_eq_right.mpr hIntTarget] at h
    exact h
  have hClosureTarget : closure (interior (e '' N)) ⊆ e.target :=
    (closure_minimal interior_subset hCompact.isClosed).trans hTarget
  have hRegularImage : closure (interior (e '' N))=e '' N := by
    have h := hImage.interior.closure.image_eq
    rw [hRegular,Set.inter_eq_right.mpr hNs,Set.inter_eq_right.mpr hClosureTarget] at h
    exact h.symm
  refine ⟨hCompact,?_,hRegularImage,hIntImage,?_⟩
  · rw [←hIntImage]
    exact hConnected.image e (e.continuousOn.mono hIntSource)
  · intro x hx
    exact hImage.frontier.apply_mem_iff hx

open Set Topology
set_option maxHeartbeats 0
private theorem actualPartialChartBoundaryHomotopyTransport
    {U : Type} [TopologicalSpace U] [T2Space U]
    (e : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin 2)))
    (N : Set U) (hN : IsCompact N) (hNs : N ⊆ e.source)
    (hFrontChart : ∀ x ∈ e.source, e x ∈ frontier (e '' N) ↔ x ∈ frontier N)
    (c : CurveComplex.Curve U) (hc : c.image ⊆ frontier N)
    (y : U) (H : ContinuousMap.Homotopy
      (⟨c.map,c.embedded.continuous⟩ : C(Circle,U)) (ContinuousMap.const Circle y))
    (hH : Set.range H ⊆ e.source)
    (V : Set U) (hV : IsOpen V) (hCV : c.image ⊆ V)
    (hFIff : ∀ x ∈ V, x ∈ frontier N ↔ x ∈ c.image) :
    ∃ cp : CurveComplex.Curve (EuclideanSpace ℝ (Fin 2)),
      cp.image=e '' c.image ∧ cp.image ⊆ frontier (e '' N) ∧
      ∃ HP : ContinuousMap.Homotopy
        (⟨cp.map,cp.embedded.continuous⟩ : C(Circle,EuclideanSpace ℝ (Fin 2)))
        (ContinuousMap.const Circle (e y)), Set.range HP ⊆ e.target ∧
      ∃ VP : Set (EuclideanSpace ℝ (Fin 2)), IsOpen VP ∧ cp.image ⊆ VP ∧
        ∀ z ∈ VP, z ∈ frontier (e '' N) ↔ z ∈ cp.image := by
  classical
  have hcSource : c.image ⊆ e.source := hc.trans (hN.isClosed.frontier_subset.trans hNs)
  let cs : Circle → e.source := fun z => ⟨c.map z,hcSource ⟨z,rfl⟩⟩
  have hcs : Continuous cs := c.embedded.continuous.subtype_mk _
  have hcsEmb : IsEmbedding cs := IsEmbedding.of_comp hcs continuous_subtype_val c.embedded
  let cp : CurveComplex.Curve (EuclideanSpace ℝ (Fin 2)) :=
    ⟨e ∘ c.map,e.isEmbedding_restrict.comp hcsEmb⟩
  have hCpImage : cp.image=e '' c.image := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨c.map t,⟨t,rfl⟩,rfl⟩
    · rintro ⟨x,⟨t,rfl⟩,rfl⟩; exact ⟨t,rfl⟩
  let HP : ContinuousMap.Homotopy
      (⟨cp.map,cp.embedded.continuous⟩ : C(Circle,EuclideanSpace ℝ (Fin 2)))
      (ContinuousMap.const Circle (e y)) := {
    toFun := fun t => e (H t)
    continuous_toFun := e.continuousOn.comp_continuous H.continuous (fun t => hH ⟨t,rfl⟩)
    map_zero_left := by
      intro t
      have ht : H (0,t)=c.map t := H.map_zero_left t
      exact congrArg e ht
    map_one_left := by
      intro t
      have ht : H (1,t)=y := H.map_one_left t
      exact congrArg e ht }
  let VP := e '' (V ∩ e.source)
  have hVp : IsOpen VP := e.isOpen_image_of_subset_source (hV.inter e.open_source) Set.inter_subset_right
  have hCpVp : cp.image ⊆ VP := by
    rw [hCpImage]
    rintro z ⟨x,hx,rfl⟩
    exact ⟨x,⟨hCV hx,hcSource hx⟩,rfl⟩
  refine ⟨cp,hCpImage,?_,HP,?_,VP,hVp,hCpVp,?_⟩
  · rw [hCpImage]
    rintro z ⟨x,hx,rfl⟩
    exact (hFrontChart x (hcSource hx)).mpr (hc hx)
  · rintro z ⟨t,rfl⟩
    exact e.map_source (hH ⟨t,rfl⟩)
  · rintro z ⟨x,hx,rfl⟩
    constructor
    · intro hFront
      rw [hCpImage]
      exact ⟨x,(hFIff x hx.1).mp ((hFrontChart x hx.2).mp hFront),rfl⟩
    · intro hCurve
      rw [hCpImage] at hCurve
      obtain ⟨w,hw,he⟩ := hCurve
      have hwx : w=x := e.injOn (hcSource hw) hx.2 he
      subst w
      exact (hFrontChart x hx.2).mpr ((hFIff x hx.1).mpr hw)

private theorem actualCompactNeighborhoodEngulfedInPartialPlaneChart
    {U : Type} [TopologicalSpace U] [T2Space U]
    (e : OpenPartialHomeomorph U Plane)
    (N K : Set U) (hN : IsCompact N) (hNs : N ⊆ e.source)
    (hConnected : IsConnected (interior N)) (hRegular : closure (interior N)=N)
    (hKN : K ⊆ interior N)
    (hBoundary : ∀ z ∈ frontier N, ∃ c : CurveComplex.Curve U,
      z ∈ c.image ∧ c.image ⊆ frontier N ∧
      ∃ y : U, ∃ H : ContinuousMap.Homotopy
        (⟨c.map,c.embedded.continuous⟩ : C(Circle,U)) (ContinuousMap.const Circle y),
        Set.range H ⊆ e.source ∧ ∃ V : Set U, IsOpen V ∧ c.image ⊆ V ∧
          ∀ x ∈ V, x ∈ frontier N ↔ x ∈ c.image) :
    ∃ D : Set U, IsCompact D ∧
      Nonempty (closedBall (0 : Plane) 1 ≃ₜ D) ∧ K ⊆ interior D := by
  classical
  obtain ⟨hA,hConnectedA,hRegularA,hIntImage,hFrontChart⟩ :=
    actualCompactPartialChartRegionTransport e N hN hNs hConnected hRegular
  have hANonempty : (e '' N).Nonempty :=
    (hConnected.nonempty.mono interior_subset).image e
  obtain ⟨z,hz,hMax⟩ := actualCompactExtremeFrontier (e '' N) hA hANonempty
  have hzA : z ∈ e '' N := hA.isClosed.frontier_subset hz
  obtain ⟨x,hx,hxz⟩ := hzA
  have hxFront : x ∈ frontier N := (hFrontChart x (hNs hx)).mp (hxz.symm ▸ hz)
  obtain ⟨c,hxc,hc,y,H,hH,V,hV,hCV,hFIff⟩ := hBoundary x hxFront
  obtain ⟨cp,hCpImage,hCpFront,HP,hHP,VP,hVP,hCpVP,hPFront⟩ :=
    actualPartialChartBoundaryHomotopyTransport e N hN hNs hFrontChart c hc y H hH V hV hCV hFIff
  have hzCp : z ∈ cp.image := by rw [hCpImage]; exact ⟨x,hxc,hxz⟩
  have hOuter : e '' N ⊆ Schoenflies.inside cp.image ∪ cp.image :=
    actualIsolatedExtremeBoundaryEngulfs (e '' N) hA.isClosed hRegularA hConnectedA
      cp hCpFront VP hVP hCpVP hPFront z hzCp hMax
  have hJ : Schoenflies.IsJordanCurve cp.image := CurveComplex.isJordanCurve_range_of_isEmbedding_circle
    (⟨cp.map,cp.embedded.continuous⟩ : C(Circle,Plane)) cp.embedded
  obtain ⟨d,hd,hdb⟩ := CurveComplex.jordan_curve_bounds_disc cp hJ
  have hdRange : Set.range d=Schoenflies.inside cp.image ∪ cp.image :=
    CurveComplex.embedded_disc_range_eq_closed_inside d hd cp.image hJ hdb
  have hCpTarget : cp.image ⊆ e.target := by
    rw [hCpImage]
    rintro q ⟨w,hw,rfl⟩
    exact e.map_source (hNs (hN.isClosed.frontier_subset (hc hw)))
  have hInsideTarget : Schoenflies.inside cp.image ⊆ e.target :=
    (CurveComplex.actual_planar_jordan_inside_subset_nullhomotopy_range cp (e y) HP).trans hHP
  have hdTarget : Set.range d ⊆ e.target := by
    rw [hdRange]
    exact Set.union_subset hInsideTarget hCpTarget
  let ds : closedBall (0 : Plane) 1 → e.target := fun t => ⟨d t,hdTarget ⟨t,rfl⟩⟩
  have hds : Continuous ds := d.continuous.subtype_mk _
  have hdsEmb : IsEmbedding ds := IsEmbedding.of_comp hds continuous_subtype_val hd
  let du : C(closedBall (0 : Plane) 1,U) :=
    ⟨e.symm ∘ d,e.symm.continuousOn.comp_continuous d.continuous (fun t => hdTarget ⟨t,rfl⟩)⟩
  have hdu : IsEmbedding du := e.symm.isEmbedding_restrict.comp hdsEmb
  let D : Set U := Set.range du
  have hD : IsCompact D := isCompact_range du.continuous
  refine ⟨D,hD,⟨hdu.toHomeomorph⟩,?_⟩
  have hInteriorInside : interior (e '' N) ⊆ Schoenflies.inside cp.image := by
    intro q hq
    rcases hOuter (interior_subset hq) with hi | hcq
    · exact hi
    · exact False.elim ((hCpFront hcq).2 hq)
  have hOpenPull : IsOpen (e.symm '' Schoenflies.inside cp.image) :=
    e.symm.isOpen_image_of_subset_source (Schoenflies.jordan_curve_theorem hJ).isOpen_inside hInsideTarget
  have hPullSub : e.symm '' Schoenflies.inside cp.image ⊆ D := by
    rintro q ⟨w,hw,rfl⟩
    have hwd : w ∈ Set.range d := by rw [hdRange]; exact Or.inl hw
    obtain ⟨t,ht⟩ := hwd
    exact ⟨t,congrArg e.symm ht⟩
  intro k hk
  have hkN := hKN hk
  have hkImage : e k ∈ interior (e '' N) := by
    rw [←hIntImage]
    exact ⟨k,hkN,rfl⟩
  apply hOpenPull.subset_interior_iff.mpr hPullSub
  exact ⟨e k,hInteriorInside hkImage,e.left_inv (hNs (interior_subset hkN))⟩
open Set Topology
set_option maxHeartbeats 0
private theorem actualEmbeddedNeighborhoodPartialPlaneChart
    {U : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U]
    (M : Set U) (hMInterior : (interior M).Nonempty)
    (f : M → EuclideanSpace ℝ (Fin 2)) (hf : IsEmbedding f) :
    ∃ e : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin 2)),
      e.source=interior M ∧ ∀ (x : U) (hx : x ∈ interior M), e x=f ⟨x,interior_subset hx⟩ := by
  classical
  let O : TopologicalSpace.Opens U := ⟨interior M,isOpen_interior⟩
  letI : Nonempty O := ⟨⟨hMInterior.choose,hMInterior.choose_spec⟩⟩
  let inc : O → M := fun x => ⟨x.val,interior_subset x.property⟩
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
  have hincEmb : IsEmbedding inc := IsEmbedding.of_comp hinc continuous_subtype_val IsEmbedding.subtypeVal
  let g : O → EuclideanSpace ℝ (Fin 2) := f ∘ inc
  have hg : IsEmbedding g := hf.comp hincEmb
  have hgOpen : IsOpenMap g := by
    intro W hW
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨x,hx,rfl⟩
    let a := chartAt (EuclideanSpace ℝ (Fin 2)) x
    let Ω := a.target ∩ a.symm ⁻¹' W
    have hΩ : IsOpen Ω := a.continuousOn_symm.isOpen_inter_preimage a.open_target hW
    have hΩTarget : Ω ⊆ a.target := Set.inter_subset_left
    have hgi : Set.InjOn (g ∘ a.symm) Ω := by
      intro u hu v hv he
      exact a.symm.injOn (hΩTarget hu) (hΩTarget hv) (hg.injective he)
    have hgc : ContinuousOn (g ∘ a.symm) Ω :=
      (hg.continuous.comp_continuousOn a.continuousOn_symm).mono hΩTarget
    have hImageOpen := CurveComplex.surface_invariance_of_domain_probe
      (g ∘ a.symm) Ω hΩ hgc hgi
    refine ⟨(g ∘ a.symm) '' Ω,?_,hImageOpen,?_⟩
    · rintro y ⟨q,hq,rfl⟩
      exact ⟨a.symm q,hq.2,rfl⟩
    · refine ⟨a x,⟨a.map_source (mem_chart_source (EuclideanSpace ℝ (Fin 2)) x),?_⟩,?_⟩
      · change a.symm (a x) ∈ W
        rw [a.left_inv (mem_chart_source (EuclideanSpace ℝ (Fin 2)) x)]
        exact hx
      · change g (a.symm (a x))=g x
        rw [a.left_inv (mem_chart_source (EuclideanSpace ℝ (Fin 2)) x)]
  have hgOpenEmb : IsOpenEmbedding g :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hg.continuous hg.injective hgOpen
  let P : OpenPartialHomeomorph O U := O.openPartialHomeomorphSubtypeCoe inferInstance
  let Q : OpenPartialHomeomorph O (EuclideanSpace ℝ (Fin 2)) := hgOpenEmb.toOpenPartialHomeomorph g
  let e := P.symm.trans Q
  have hSource : e.source=interior M := by
    change P.target ∩ P.symm ⁻¹' Q.source=interior M
    simp [P,Q,O]
  refine ⟨e,hSource,?_⟩
  intro x hx
  have hP : P.symm x=(⟨x,hx⟩ : O) := by
    have h := P.left_inv (show (⟨x,hx⟩ : O) ∈ P.source from Set.mem_univ _)
    exact h
  change g (P.symm x)=f ⟨x,interior_subset hx⟩
  rw [hP]
  rfl
end OriginalPartialPlaneEngulfing

namespace CurveComplex.LocalSurgery
open scoped Manifold ContDiff
open Real Set Metric Topology LeanEval.Topology.ClassificationOfSurfaces
open SurfaceCellComplex FiniteCyclicPresentation
open ClassificationJordanCurve.Arcs
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
open LeanEval.Topology.ClassificationOfSurfaces.Moise hiding Plane
open LeanEval.Topology.ClassificationOfSurfaces.Moise.PartialTriangulation
local macro "diskSourcePrivate" n:ident : term => do
  let sourcePrefix := Lean.Name.num `_private.ClassificationOfSurfaces.Moise.ChartInductionCore 0
  let scope := `LeanEval.Topology.ClassificationOfSurfaces.Moise.PartialTriangulation
  return Lean.mkIdent (sourcePrefix ++ scope ++ n.getId)
local macro "diskWeldPrivate" n:ident : term => do
  let sourcePrefix := Lean.Name.num `_private.ClassificationOfSurfaces.Moise.ChartInduction 0
  let scope := `LeanEval.Topology.ClassificationOfSurfaces.Moise
  return Lean.mkIdent (sourcePrefix ++ scope ++ n.getId)

theorem closed_surface_simply_connected_cover_plane_or_sphere
    {S U : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    [TopologicalSpace U] [T2Space U] [SecondCountableTopology U]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U] [SimplyConnectedSpace U]
    (p : U → S) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ U) ∨
      Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₜ U) := by
  letI : LocallyPathConnectedSpace U :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) U
  by_cases hCompact : IsCompact (Set.univ : Set U)
  · letI : CompactSpace U := isCompact_univ_iff.mp hCompact
    have compactModels {U : Type} [TopologicalSpace U] [T2Space U] [CompactSpace U]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U] [SimplyConnectedSpace U] :
        Nonempty (SphereRepresentative ≃ₜ U) ∨
          Nonempty ((Quot (NonOrientableRel 1 0)) ≃ₜ U) := by
      have three {U : Type} [TopologicalSpace U] [T2Space U] [CompactSpace U]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U] [SimplyConnectedSpace U] :
          Nonempty (SphereRepresentative ≃ₜ U) ∨
            Nonempty ((Quot (OrientableRel 0 1)) ≃ₜ U) ∨
            Nonempty ((Quot (NonOrientableRel 1 0)) ≃ₜ U) := by
        have ho (p n : ℕ) (hp : 1 ≤ p) : ¬ SimplyConnectedSpace (Quot (OrientableRel p n)) := by
          have phase : ∃ ψ : C(Complex.ClosedUnitDisc,ℝ),
              (∀ x y, OrientableRel p n x y → ∃ k : ℤ, ψ x - ψ y = (k : ℝ)) ∧
              (∀ t ∈ Icc (0 : ℝ) 1,
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (t / (4*p+3*n))) = t) := by
            have build (N peak width : ℝ) (hpeak : 0 ≤ peak) (hwidth : 0 ≤ width)
                (hN : width ≤ N) :
                ∃ φ : C(Circle,ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
                  φ (Real.fourierChar t) = max 0 (min peak (min (N*t) (width-N*t))) := by
              have build : ∃ φ : C(AddCircle (1 : ℝ),ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
                  φ (t : AddCircle (1 : ℝ)) = max 0 (min peak (min (N*t) (width-N*t))) := by
                let u : ℝ → ℝ := fun t => max 0 (min peak (min (N*t) (width-N*t)))
                have h0 : u 0 = 0 := by simp [u, hwidth, hpeak]
                have h1 : u 1 = 0 := by
                  apply max_eq_left
                  exact (min_le_right _ _).trans ((min_le_right _ _).trans
                    (by simpa only [mul_one] using sub_nonpos.mpr hN))
                have he : u 0 = u (0+1) := by simpa only [zero_add,h0,h1]
                have hc : Continuous u := by
                  exact continuous_const.max (continuous_const.min
                    ((continuous_const.mul continuous_id).min
                      (continuous_const.sub (continuous_const.mul continuous_id))))
                let φ : C(AddCircle (1 : ℝ),ℝ) :=
                  ⟨AddCircle.liftIco (1 : ℝ) 0 u, AddCircle.liftIco_continuous he hc.continuousOn⟩
                refine ⟨φ, ?_⟩
                intro t ht
                rcases lt_or_eq_of_le ht.2 with hlt | rfl
                · change AddCircle.liftIco (1 : ℝ) 0 u (t : AddCircle (1 : ℝ)) = u t
                  exact AddCircle.liftIco_coe_apply (by simpa only [zero_add, Set.mem_Ico] using And.intro ht.1 hlt)
                · have hz : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
                  rw [hz]
                  change AddCircle.liftIco (1 : ℝ) 0 u (0 : AddCircle (1 : ℝ)) = u 1
                  rw [← AddCircle.coe_zero, AddCircle.liftIco_coe_apply (by norm_num),h0,h1]
              obtain ⟨φ,hφ⟩ := build
              let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
              let ψ : C(Circle,ℝ) := φ.comp ⟨H.symm,H.symm.continuous⟩
              have hparam (t : ℝ) : H (t : AddCircle (1 : ℝ)) = Real.fourierChar t := by
                simp only [H, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
                  div_one, Real.fourierChar_apply']
              refine ⟨ψ, ?_⟩
              intro t ht
              change φ (H.symm (Real.fourierChar t)) = _
              rw [← hparam t, H.symm_apply_apply]
              exact hφ t ht
            have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
            let N : ℝ := 4*p+3*n
            have hnR : (0 : ℝ) ≤ n := by positivity
            have hN : 4 ≤ N := by dsimp [N]; linarith
            have hNpos : 0 < N := by linarith
            obtain ⟨φ,hφ⟩ := build N 1 3 (by norm_num) (by norm_num) (by linarith)
            let e : Circle → Complex.ClosedUnitDisc := fun z => ⟨z, by simp⟩
            have hec : Continuous e := continuous_subtype_val.subtype_mk _
            have hei : Function.Injective e := by
              intro x y h
              exact Subtype.ext (congrArg (fun z : Complex.ClosedUnitDisc => (z : ℂ)) h)
            have he : IsClosedEmbedding e := hec.isClosedEmbedding hei
            obtain ⟨ψ,hψ⟩ := φ.exists_extension he
            have agrees (z : Circle) : ψ (e z) = φ z := congrArg (fun f : C(Circle,ℝ) => f z) hψ
            let q : ℝ → ℝ := fun r => max 0 (min 1 (min r (3-r)))
            have value (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (r/N)) = q r := by
              change ψ (e (Real.fourierChar (r/N))) = q r
              rw [agrees]
              have ht : r/N ∈ Icc (0 : ℝ) 1 :=
                ⟨div_nonneg hr0 hNpos.le, (div_le_one hNpos).mpr hrN⟩
              rw [hφ _ ht]
              dsimp [q]
              rw [mul_div_cancel₀ r hNpos.ne']
            have valueNeg (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-r/N)) = q (N-r) := by
              have hperiod := Complex.ClosedUnitDisc.bdyPtOfReal_add_int (-r/N) 1
              have hh : -r/N + (1:ℤ) = (N-r)/N := by field_simp; ring
              rw [hh] at hperiod
              rw [← hperiod]
              exact value _ (by linarith) (by linarith)
            have qlow (t : ℝ) (ht : t ∈ Icc 0 1) : q t = t := by
              dsimp [q]
              rw [min_eq_left (by linarith [ht.2] : t ≤ 3-t), min_eq_right ht.2, max_eq_right ht.1]
            have qhigh (r : ℝ) (hr : 3 ≤ r) : q r = 0 := by
              dsimp [q]
              apply max_eq_left
              exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))
            refine ⟨ψ, ?_, ?_⟩
            · intro x y hxy
              cases hxy with
              | a t i =>
                have hi : (i : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
                have hi0 : (0 : ℝ) ≤ i := by positivity
                have ht0 := t.property.1
                have ht1 := t.property.2
                change ∃ k : ℤ,
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+(t:ℝ))/N)) -
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+3-(t:ℝ))/N)) = (k:ℝ)
                rw [value _ (by linarith) (by dsimp [N]; linarith),
                    value _ (by linarith) (by dsimp [N]; linarith)]
                by_cases hz : i.val = 0
                · have hi' : (i : ℝ) = 0 := by exact_mod_cast hz
                  rw [hi']; simp only [mul_zero,zero_add]
                  rw [qlow _ t.property]
                  have hq : q (3-(t:ℝ)) = (t:ℝ) := by
                    dsimp [q]
                    rw [min_eq_right (by linarith : 3-(t:ℝ) ≥ 3-(3-(t:ℝ)))]
                    have hh : 3-(3-(t:ℝ)) = (t:ℝ) := by ring
                    rw [hh,min_eq_right ht1,max_eq_right ht0]
                  rw [hq]
                  exact ⟨0,by simp⟩
                · have hi' : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i.val by omega)
                  rw [qhigh _ (by linarith), qhigh _ (by linarith)]
                  exact ⟨0,by simp⟩
              | b t i =>
                have hi : (i : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
                have hi0 : (0 : ℝ) ≤ i := by positivity
                have ht0 := t.property.1
                have ht1 := t.property.2
                change ∃ k : ℤ,
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+1+(t:ℝ))/N)) -
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+4-(t:ℝ))/N)) = (k:ℝ)
                rw [value _ (by linarith) (by dsimp [N]; linarith),
                    value _ (by linarith) (by dsimp [N]; linarith)]
                by_cases hz : i.val = 0
                · have hi' : (i : ℝ) = 0 := by exact_mod_cast hz
                  rw [hi']; simp only [mul_zero,zero_add]
                  have hq : q (1+(t:ℝ)) = 1 := by
                    dsimp [q]
                    rw [min_eq_left (le_min (by linarith) (by linarith)), max_eq_right (by norm_num)]
                  rw [hq,qhigh _ (by linarith)]
                  exact ⟨1,by simp⟩
                · have hi' : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i.val by omega)
                  rw [qhigh _ (by linarith), qhigh _ (by linarith)]
                  exact ⟨0,by simp⟩
              | c t i =>
                have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
                have hi0 : (0 : ℝ) ≤ i := by positivity
                have ht0 := t.property.1
                have ht1 := t.property.2
                change ∃ k : ℤ,
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+(t:ℝ))/N)) -
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+3-(t:ℝ))/N)) = (k:ℝ)
                rw [valueNeg _ (by linarith) (by dsimp [N]; linarith),
                    valueNeg _ (by linarith) (by dsimp [N]; linarith)]
                rw [qhigh _ (by dsimp [N]; linarith), qhigh _ (by dsimp [N]; linarith)]
                exact ⟨0,by simp⟩
            · intro t ht
              change ψ (Complex.ClosedUnitDisc.bdyPtOfReal (t/N)) = t
              rw [value t ht.1 (by linarith [ht.2]), qlow t ht]
          have construct {X : Type} [TopologicalSpace X] (R : X → X → Prop)
              (φ : C(X,ℝ))
              (hφ : ∀ x y, R x y → ∃ k : ℤ, φ x - φ y = (k : ℝ))
              (σ : ℝ → X) (hσ : ContinuousOn σ (Icc 0 1))
              (hends : Quot.mk R (σ 0) = Quot.mk R (σ 1))
              (hphase : ∀ t ∈ Icc (0 : ℝ) 1, φ (σ t) = t) :
              ∃ f : C(Quot R,Circle), ∃ g : C(Circle,Quot R), ∀ z, f (g z) = z := by
            have construct (F : C(X,Circle)) (hF : ∀ x y, R x y → F x = F y)
                (hwind : ∀ t ∈ Icc (0 : ℝ) 1,
                  F (σ t) = AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
                    (t : AddCircle (1 : ℝ))) :
                ∃ f : C(Quot R,Circle), ∃ g : C(Circle,Quot R), ∀ z, f (g z) = z := by
              let f : C(Quot R,Circle) := ⟨Quot.lift F hF, continuous_quot_lift hF F.continuous⟩
              let q : ℝ → Quot R := fun t => Quot.mk R (σ t)
              have he : q 0 = q (0+1) := by
                simpa only [q, zero_add] using hends
              have hc : ContinuousOn q (Icc 0 (0+1)) := by
                simpa only [zero_add, q, Function.comp_def] using
                  (continuous_quot_mk (r := R)).comp_continuousOn hσ
              let a : C(AddCircle (1 : ℝ),Quot R) :=
                ⟨AddCircle.liftIco (1 : ℝ) 0 q, AddCircle.liftIco_continuous he hc⟩
              have ha (z : AddCircle (1 : ℝ)) : f (a z) = AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero z := by
                let t := AddCircle.equivIco (1 : ℝ) 0 z
                have ht : (t : ℝ) ∈ Ico (0 : ℝ) 1 := by simpa only [zero_add] using t.property
                have hz : ((t : ℝ) : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco
                rw [← hz]
                change Quot.lift F hF (AddCircle.liftIco (1 : ℝ) 0 q (t : ℝ)) = _
                rw [AddCircle.liftIco_coe_apply (by simpa only [zero_add] using ht)]
                exact hwind t ⟨ht.1,le_of_lt ht.2⟩
              let g : C(Circle,Quot R) := a.comp ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm,
                  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous⟩
              exact ⟨f,g,fun z => (ha _).trans ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply z)⟩
            let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
            let F : C(X,Circle) := ⟨fun x => H (φ x : AddCircle (1 : ℝ)),
              H.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp φ.continuous)⟩
            apply construct F
            · intro x y hxy
              apply congrArg H
              apply QuotientAddGroup.eq_iff_sub_mem.mpr
              obtain ⟨k,hk⟩ := hφ x y hxy
              apply AddSubgroup.mem_zmultiples_iff.mpr
              exact ⟨k, by simpa only [zsmul_eq_mul, mul_one] using hk.symm⟩
            · intro t ht
              change H (φ (σ t) : AddCircle (1 : ℝ)) = H (t : AddCircle (1 : ℝ))
              rw [hphase t ht]
          have obstruction {U : Type} [TopologicalSpace U] [SimplyConnectedSpace U]
              (f : U → Circle) (g : Circle → U) (hf : Continuous f) (hg : Continuous g)
              (hfg : Function.RightInverse g f) : False := by
            have circleObstruction : ¬ SimplyConnectedSpace Circle := by
              intro h
              letI : SimplyConnectedSpace Circle := h
              let G := AddSubgroup.zmultiples (2 * π)
              let e := Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
                (x := Circle.exp 0) ⟨0, rfl⟩
              let a : G := ⟨0, (AddSubgroup.zmultiples (2 * π)).zero_mem⟩
              let b : G := ⟨2 * π, AddSubgroup.mem_zmultiples (2 * π)⟩
              have hab : MulOpposite.op (Multiplicative.ofAdd a) =
                  MulOpposite.op (Multiplicative.ofAdd b) := by
                apply e.symm.injective
                exact Subsingleton.elim _ _
              have hv : (0 : ℝ) = 2 * π :=
                congrArg (fun z : (Multiplicative G)ᵐᵒᵖ => ((MulOpposite.unop z).toAdd : ℝ)) hab
              have := Real.pi_pos
              linarith
            have retract : SimplyConnectedSpace Circle := by
              have hcomp : f ∘ g = id := funext hfg
              letI : PathConnectedSpace Circle := hfg.surjective.pathConnectedSpace hf
              apply simply_connected_iff_paths_homotopic'.mpr
              refine ⟨inferInstance, ?_⟩
              intro x y p q
              have H := (SimplyConnectedSpace.paths_homotopic (p.map hg) (q.map hg)).map
                (⟨f,hf⟩ : C(U,Circle))
              change Path.Homotopic ((p.map hg).map hf) ((q.map hg).map hf) at H
              have H' := H.pathCast (hfg x).symm (hfg y).symm
              have hp : (((p.map hg).map hf).cast (hfg x).symm (hfg y).symm) = p := by
                ext t
                exact congrArg Subtype.val (hfg (p t))
              have hq : (((q.map hg).map hf).cast (hfg x).symm (hfg y).symm) = q := by
                ext t
                exact congrArg Subtype.val (hfg (q t))
              rwa [hp,hq] at H'
            exact circleObstruction retract
          intro h
          letI : SimplyConnectedSpace (Quot (OrientableRel p n)) := h
          obtain ⟨ψ,hψ,hphase⟩ := phase
          let R := OrientableRel p n
          let σ : ℝ → Complex.ClosedUnitDisc :=
            fun t => Complex.ClosedUnitDisc.bdyPtOfReal (t/(4*p+3*n))
          have hc : Continuous σ := by
            apply Continuous.subtype_mk
            exact continuous_subtype_val.comp
              (Real.continuous_fourierChar.comp (continuous_id.div_const (4*(p:ℝ)+3*n)))
          let i : Fin p := ⟨0,by omega⟩
          have ha0 := Quot.sound (OrientableRel.a (p := p) (n := n) (⟨0,by norm_num⟩ : Icc (0:ℝ) 1) i)
          have hb1 := Quot.sound (OrientableRel.b (p := p) (n := n) (⟨1,by norm_num⟩ : Icc (0:ℝ) 1) i)
          have ha1 := Quot.sound (OrientableRel.a (p := p) (n := n) (⟨1,by norm_num⟩ : Icc (0:ℝ) 1) i)
          norm_num [i] at ha0 hb1 ha1
          have he : Quot.mk R (σ 0) = Quot.mk R (σ 1) := by
            simpa [σ, R, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              ha0.trans (hb1.symm.trans ha1.symm)
          obtain ⟨f,g,hfg⟩ := construct R ψ hψ σ hc.continuousOn he hphase
          exact obstruction f g f.continuous g.continuous hfg
        have hn (p n : ℕ) (hp : 2 ≤ p) : ¬ SimplyConnectedSpace (Quot (NonOrientableRel p n)) := by
          have phase : ∃ ψ : C(Complex.ClosedUnitDisc,ℝ),
              (∀ x y, NonOrientableRel p n x y → ∃ k : ℤ, ψ x - ψ y = (k : ℝ)) ∧
              (∀ t ∈ Icc (0 : ℝ) 1,
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (t / (2*p+3*n))) = t) := by
            have build (N peak width : ℝ) (hpeak : 0 ≤ peak) (hwidth : 0 ≤ width)
                (hN : width ≤ N) :
                ∃ φ : C(Circle,ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
                  φ (Real.fourierChar t) = max 0 (min peak (min (N*t) (width-N*t))) := by
              have build : ∃ φ : C(AddCircle (1 : ℝ),ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
                  φ (t : AddCircle (1 : ℝ)) = max 0 (min peak (min (N*t) (width-N*t))) := by
                let u : ℝ → ℝ := fun t => max 0 (min peak (min (N*t) (width-N*t)))
                have h0 : u 0 = 0 := by simp [u, hwidth, hpeak]
                have h1 : u 1 = 0 := by
                  apply max_eq_left
                  exact (min_le_right _ _).trans ((min_le_right _ _).trans
                    (by simpa only [mul_one] using sub_nonpos.mpr hN))
                have he : u 0 = u (0+1) := by simpa only [zero_add,h0,h1]
                have hc : Continuous u := by
                  exact continuous_const.max (continuous_const.min
                    ((continuous_const.mul continuous_id).min
                      (continuous_const.sub (continuous_const.mul continuous_id))))
                let φ : C(AddCircle (1 : ℝ),ℝ) :=
                  ⟨AddCircle.liftIco (1 : ℝ) 0 u, AddCircle.liftIco_continuous he hc.continuousOn⟩
                refine ⟨φ, ?_⟩
                intro t ht
                rcases lt_or_eq_of_le ht.2 with hlt | rfl
                · change AddCircle.liftIco (1 : ℝ) 0 u (t : AddCircle (1 : ℝ)) = u t
                  exact AddCircle.liftIco_coe_apply (by simpa only [zero_add, Set.mem_Ico] using And.intro ht.1 hlt)
                · have hz : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
                  rw [hz]
                  change AddCircle.liftIco (1 : ℝ) 0 u (0 : AddCircle (1 : ℝ)) = u 1
                  rw [← AddCircle.coe_zero, AddCircle.liftIco_coe_apply (by norm_num),h0,h1]
              obtain ⟨φ,hφ⟩ := build
              let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
              let ψ : C(Circle,ℝ) := φ.comp ⟨H.symm,H.symm.continuous⟩
              have hparam (t : ℝ) : H (t : AddCircle (1 : ℝ)) = Real.fourierChar t := by
                simp only [H, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
                  div_one, Real.fourierChar_apply']
              refine ⟨ψ, ?_⟩
              intro t ht
              change φ (H.symm (Real.fourierChar t)) = _
              rw [← hparam t, H.symm_apply_apply]
              exact hφ t ht
            have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
            let N : ℝ := 2*p+3*n
            have hnR : (0 : ℝ) ≤ n := by positivity
            have hN : 4 ≤ N := by dsimp [N]; linarith
            have hNpos : 0 < N := by linarith
            obtain ⟨φ,hφ⟩ := build N 2 4 (by norm_num) (by norm_num) (by linarith)
            let e : Circle → Complex.ClosedUnitDisc := fun z => ⟨z, by simp⟩
            have hec : Continuous e := continuous_subtype_val.subtype_mk _
            have hei : Function.Injective e := by
              intro x y h
              exact Subtype.ext (congrArg (fun z : Complex.ClosedUnitDisc => (z : ℂ)) h)
            have he : IsClosedEmbedding e := hec.isClosedEmbedding hei
            obtain ⟨ψ,hψ⟩ := φ.exists_extension he
            have agrees (z : Circle) : ψ (e z) = φ z := congrArg (fun f : C(Circle,ℝ) => f z) hψ
            let q : ℝ → ℝ := fun r => max 0 (min 2 (min r (4-r)))
            have value (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (r/N)) = q r := by
              change ψ (e (Real.fourierChar (r/N))) = q r
              rw [agrees]
              have ht : r/N ∈ Icc (0 : ℝ) 1 :=
                ⟨div_nonneg hr0 hNpos.le, (div_le_one hNpos).mpr hrN⟩
              rw [hφ _ ht]
              dsimp [q]
              rw [mul_div_cancel₀ r hNpos.ne']
            have valueNeg (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-r/N)) = q (N-r) := by
              have hperiod := Complex.ClosedUnitDisc.bdyPtOfReal_add_int (-r/N) 1
              have hh : -r/N + (1:ℤ) = (N-r)/N := by field_simp; ring
              rw [hh] at hperiod
              rw [← hperiod]
              exact value _ (by linarith) (by linarith)
            have qlow (t : ℝ) (ht : t ∈ Icc 0 1) : q t = t := by
              dsimp [q]
              rw [min_eq_left (by linarith [ht.2] : t ≤ 4-t), min_eq_right (by linarith [ht.2] : t ≤ 2), max_eq_right ht.1]
            have qhigh (r : ℝ) (hr : 4 ≤ r) : q r = 0 := by
              dsimp [q]
              apply max_eq_left
              exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))
            refine ⟨ψ, ?_, ?_⟩
            · intro x y hxy
              cases hxy with
              | a t i =>
                have hi : (i : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
                have hi0 : (0 : ℝ) ≤ i := by positivity
                have ht0 := t.property.1
                have ht1 := t.property.2
                change ∃ k : ℤ,
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((2*(i:ℝ)+(t:ℝ))/N)) -
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((2*(i:ℝ)+1+(t:ℝ))/N)) = (k:ℝ)
                rw [value _ (by linarith) (by dsimp [N]; linarith),
                    value _ (by linarith) (by dsimp [N]; linarith)]
                by_cases hz : i.val = 0
                · have hi' : (i : ℝ) = 0 := by exact_mod_cast hz
                  rw [hi']; simp only [mul_zero,zero_add]
                  rw [qlow _ t.property]
                  have hq : q (1+(t:ℝ)) = 1+(t:ℝ) := by
                    dsimp [q]
                    rw [min_eq_left (by linarith : 1+(t:ℝ) ≤ 4-(1+(t:ℝ))),
                      min_eq_right (by linarith : 1+(t:ℝ) ≤ 2), max_eq_right (by linarith)]
                  rw [hq]
                  exact ⟨-1,by ring⟩
                · by_cases hz1 : i.val = 1
                  · have hi' : (i : ℝ) = 1 := by exact_mod_cast hz1
                    rw [hi']; norm_num only [mul_one]
                    have hq2 : q (2+(t:ℝ)) = 2-(t:ℝ) := by
                      dsimp [q]
                      rw [min_eq_right (by linarith : 4-(2+(t:ℝ)) ≤ 2+(t:ℝ))]
                      have hh : 4-(2+(t:ℝ)) = 2-(t:ℝ) := by ring
                      rw [hh, min_eq_right (by linarith), max_eq_right (by linarith)]
                    have hq3 : q (3+(t:ℝ)) = 1-(t:ℝ) := by
                      dsimp [q]
                      rw [min_eq_right (by linarith : 4-(3+(t:ℝ)) ≤ 3+(t:ℝ))]
                      have hh : 4-(3+(t:ℝ)) = 1-(t:ℝ) := by ring
                      rw [hh, min_eq_right (by linarith), max_eq_right (by linarith)]
                    rw [hq2,hq3]
                    exact ⟨1,by ring⟩
                  · have hi' : (2 : ℝ) ≤ i := by exact_mod_cast (show 2 ≤ i.val by omega)
                    rw [qhigh _ (by linarith), qhigh _ (by linarith)]
                    exact ⟨0,by simp⟩
              | c t i =>
                have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
                have hi0 : (0 : ℝ) ≤ i := by positivity
                have ht0 := t.property.1
                have ht1 := t.property.2
                change ∃ k : ℤ,
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+(t:ℝ))/N)) -
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+3-(t:ℝ))/N)) = (k:ℝ)
                rw [valueNeg _ (by linarith) (by dsimp [N]; linarith),
                    valueNeg _ (by linarith) (by dsimp [N]; linarith)]
                rw [qhigh _ (by dsimp [N]; linarith), qhigh _ (by dsimp [N]; linarith)]
                exact ⟨0,by simp⟩
            · intro t ht
              change ψ (Complex.ClosedUnitDisc.bdyPtOfReal (t/N)) = t
              rw [value t ht.1 (by linarith [ht.2]), qlow t ht]
          have construct {X : Type} [TopologicalSpace X] (R : X → X → Prop)
              (φ : C(X,ℝ))
              (hφ : ∀ x y, R x y → ∃ k : ℤ, φ x - φ y = (k : ℝ))
              (σ : ℝ → X) (hσ : ContinuousOn σ (Icc 0 1))
              (hends : Quot.mk R (σ 0) = Quot.mk R (σ 1))
              (hphase : ∀ t ∈ Icc (0 : ℝ) 1, φ (σ t) = t) :
              ∃ f : C(Quot R,Circle), ∃ g : C(Circle,Quot R), ∀ z, f (g z) = z := by
            have construct (F : C(X,Circle)) (hF : ∀ x y, R x y → F x = F y)
                (hwind : ∀ t ∈ Icc (0 : ℝ) 1,
                  F (σ t) = AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
                    (t : AddCircle (1 : ℝ))) :
                ∃ f : C(Quot R,Circle), ∃ g : C(Circle,Quot R), ∀ z, f (g z) = z := by
              let f : C(Quot R,Circle) := ⟨Quot.lift F hF, continuous_quot_lift hF F.continuous⟩
              let q : ℝ → Quot R := fun t => Quot.mk R (σ t)
              have he : q 0 = q (0+1) := by
                simpa only [q, zero_add] using hends
              have hc : ContinuousOn q (Icc 0 (0+1)) := by
                simpa only [zero_add, q, Function.comp_def] using
                  (continuous_quot_mk (r := R)).comp_continuousOn hσ
              let a : C(AddCircle (1 : ℝ),Quot R) :=
                ⟨AddCircle.liftIco (1 : ℝ) 0 q, AddCircle.liftIco_continuous he hc⟩
              have ha (z : AddCircle (1 : ℝ)) : f (a z) = AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero z := by
                let t := AddCircle.equivIco (1 : ℝ) 0 z
                have ht : (t : ℝ) ∈ Ico (0 : ℝ) 1 := by simpa only [zero_add] using t.property
                have hz : ((t : ℝ) : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco
                rw [← hz]
                change Quot.lift F hF (AddCircle.liftIco (1 : ℝ) 0 q (t : ℝ)) = _
                rw [AddCircle.liftIco_coe_apply (by simpa only [zero_add] using ht)]
                exact hwind t ⟨ht.1,le_of_lt ht.2⟩
              let g : C(Circle,Quot R) := a.comp ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm,
                  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous⟩
              exact ⟨f,g,fun z => (ha _).trans ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply z)⟩
            let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
            let F : C(X,Circle) := ⟨fun x => H (φ x : AddCircle (1 : ℝ)),
              H.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp φ.continuous)⟩
            apply construct F
            · intro x y hxy
              apply congrArg H
              apply QuotientAddGroup.eq_iff_sub_mem.mpr
              obtain ⟨k,hk⟩ := hφ x y hxy
              apply AddSubgroup.mem_zmultiples_iff.mpr
              exact ⟨k, by simpa only [zsmul_eq_mul, mul_one] using hk.symm⟩
            · intro t ht
              change H (φ (σ t) : AddCircle (1 : ℝ)) = H (t : AddCircle (1 : ℝ))
              rw [hphase t ht]
          have obstruction {U : Type} [TopologicalSpace U] [SimplyConnectedSpace U]
              (f : U → Circle) (g : Circle → U) (hf : Continuous f) (hg : Continuous g)
              (hfg : Function.RightInverse g f) : False := by
            have circleObstruction : ¬ SimplyConnectedSpace Circle := by
              intro h
              letI : SimplyConnectedSpace Circle := h
              let G := AddSubgroup.zmultiples (2 * π)
              let e := Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
                (x := Circle.exp 0) ⟨0, rfl⟩
              let a : G := ⟨0, (AddSubgroup.zmultiples (2 * π)).zero_mem⟩
              let b : G := ⟨2 * π, AddSubgroup.mem_zmultiples (2 * π)⟩
              have hab : MulOpposite.op (Multiplicative.ofAdd a) =
                  MulOpposite.op (Multiplicative.ofAdd b) := by
                apply e.symm.injective
                exact Subsingleton.elim _ _
              have hv : (0 : ℝ) = 2 * π :=
                congrArg (fun z : (Multiplicative G)ᵐᵒᵖ => ((MulOpposite.unop z).toAdd : ℝ)) hab
              have := Real.pi_pos
              linarith
            have retract : SimplyConnectedSpace Circle := by
              have hcomp : f ∘ g = id := funext hfg
              letI : PathConnectedSpace Circle := hfg.surjective.pathConnectedSpace hf
              apply simply_connected_iff_paths_homotopic'.mpr
              refine ⟨inferInstance, ?_⟩
              intro x y p q
              have H := (SimplyConnectedSpace.paths_homotopic (p.map hg) (q.map hg)).map
                (⟨f,hf⟩ : C(U,Circle))
              change Path.Homotopic ((p.map hg).map hf) ((q.map hg).map hf) at H
              have H' := H.pathCast (hfg x).symm (hfg y).symm
              have hp : (((p.map hg).map hf).cast (hfg x).symm (hfg y).symm) = p := by
                ext t
                exact congrArg Subtype.val (hfg (p t))
              have hq : (((q.map hg).map hf).cast (hfg x).symm (hfg y).symm) = q := by
                ext t
                exact congrArg Subtype.val (hfg (q t))
              rwa [hp,hq] at H'
            exact circleObstruction retract
          intro h
          letI : SimplyConnectedSpace (Quot (NonOrientableRel p n)) := h
          obtain ⟨ψ,hψ,hphase⟩ := phase
          let R := NonOrientableRel p n
          let σ : ℝ → Complex.ClosedUnitDisc :=
            fun t => Complex.ClosedUnitDisc.bdyPtOfReal (t/(2*p+3*n))
          have hc : Continuous σ := by
            apply Continuous.subtype_mk
            exact continuous_subtype_val.comp
              (Real.continuous_fourierChar.comp (continuous_id.div_const (2*(p:ℝ)+3*n)))
          let i : Fin p := ⟨0,by omega⟩
          have ha0 := Quot.sound (NonOrientableRel.a (p := p) (n := n)
            (⟨0,by norm_num⟩ : Icc (0:ℝ) 1) i)
          norm_num [i] at ha0
          have he : Quot.mk R (σ 0) = Quot.mk R (σ 1) := by
            simpa [σ, R, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ha0
          obtain ⟨f,g,hfg⟩ := construct R ψ hψ σ hc.continuousOn he hphase
          exact obstruction f g f.continuous g.continuous hfg
        have hnb (n : ℕ) (hn : 1 ≤ n) : ¬ SimplyConnectedSpace (Quot (NonOrientableRel 1 n)) := by
          have phase : ∃ ψ : C(Complex.ClosedUnitDisc,ℝ),
              (∀ x y, NonOrientableRel 1 n x y → ∃ k : ℤ, ψ x - ψ y = (k : ℝ)) ∧
              (∀ t ∈ Icc (0 : ℝ) 1,
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (t/(2+3*n))) = t) := by
            have build (N peak start width slope : ℝ) (hstart : 0 ≤ start)
                (hend : width ≤ slope*N) :
                ∃ φ : C(Circle,ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
                  φ (Real.fourierChar t) = max 0 (min peak (min (N*t-start) (width-slope*N*t))) := by
              have build : ∃ φ : C(AddCircle (1 : ℝ),ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
                  φ (t : AddCircle (1 : ℝ)) = max 0 (min peak (min (N*t-start) (width-slope*N*t))) := by
                let u : ℝ → ℝ := fun t => max 0 (min peak (min (N*t-start) (width-slope*N*t)))
                have h0 : u 0 = 0 := by
                  apply max_eq_left
                  exact (min_le_right _ _).trans ((min_le_left _ _).trans
                    (by simpa only [mul_zero, zero_sub] using neg_nonpos.mpr hstart))
                have h1 : u 1 = 0 := by
                  apply max_eq_left
                  exact (min_le_right _ _).trans ((min_le_right _ _).trans
                    (by simpa only [mul_one] using sub_nonpos.mpr hend))
                have he : u 0 = u (0+1) := by simpa only [zero_add,h0,h1]
                have hc : Continuous u := by
                  dsimp [u]
                  fun_prop
                let φ : C(AddCircle (1 : ℝ),ℝ) :=
                  ⟨AddCircle.liftIco (1 : ℝ) 0 u, AddCircle.liftIco_continuous he hc.continuousOn⟩
                refine ⟨φ, ?_⟩
                intro t ht
                rcases lt_or_eq_of_le ht.2 with hlt | rfl
                · change AddCircle.liftIco (1 : ℝ) 0 u (t : AddCircle (1 : ℝ)) = u t
                  exact AddCircle.liftIco_coe_apply (by simpa only [zero_add, Set.mem_Ico] using And.intro ht.1 hlt)
                · have hz : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
                  rw [hz]
                  change AddCircle.liftIco (1 : ℝ) 0 u (0 : AddCircle (1 : ℝ)) = u 1
                  rw [← AddCircle.coe_zero, AddCircle.liftIco_coe_apply (by norm_num),h0,h1]
              obtain ⟨φ,hφ⟩ := build
              let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
              let ψ : C(Circle,ℝ) := φ.comp ⟨H.symm,H.symm.continuous⟩
              have hparam (t : ℝ) : H (t : AddCircle (1 : ℝ)) = Real.fourierChar t := by
                simp only [H, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
                  div_one, Real.fourierChar_apply']
              refine ⟨ψ, ?_⟩
              intro t ht
              change φ (H.symm (Real.fourierChar t)) = _
              rw [← hparam t, H.symm_apply_apply]
              exact hφ t ht
            have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
            let N : ℝ := 2+3*n
            have hN : 5 ≤ N := by dsimp [N]; linarith
            have hNpos : 0 < N := by linarith
            obtain ⟨φ,hφ⟩ := build N 2 0 8 2 (by norm_num) (by linarith)
            let e : Circle → Complex.ClosedUnitDisc := fun z => ⟨z, by simp⟩
            have hec : Continuous e := continuous_subtype_val.subtype_mk _
            have hei : Function.Injective e := by
              intro x y h
              exact Subtype.ext (congrArg (fun z : Complex.ClosedUnitDisc => (z : ℂ)) h)
            have he : IsClosedEmbedding e := hec.isClosedEmbedding hei
            obtain ⟨ψ,hψ⟩ := φ.exists_extension he
            have agrees (z : Circle) : ψ (e z) = φ z := congrArg (fun f : C(Circle,ℝ) => f z) hψ
            let q : ℝ → ℝ := fun r => max 0 (min 2 (min r (8-2*r)))
            have value (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (r/N)) = q r := by
              change ψ (e (Real.fourierChar (r/N))) = q r
              rw [agrees]
              have ht : r/N ∈ Icc (0 : ℝ) 1 :=
                ⟨div_nonneg hr0 hNpos.le, (div_le_one hNpos).mpr hrN⟩
              rw [hφ _ ht]
              dsimp [q]
              rw [mul_assoc 2 N (r/N),mul_div_cancel₀ r hNpos.ne']
              simp only [sub_zero]
            have valueNeg (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-r/N)) = q (N-r) := by
              have hperiod := Complex.ClosedUnitDisc.bdyPtOfReal_add_int (-r/N) 1
              have hh : -r/N + (1:ℤ) = (N-r)/N := by field_simp; ring
              rw [hh] at hperiod
              rw [← hperiod]
              exact value _ (by linarith) (by linarith)
            have qlow (t : ℝ) (ht : t ∈ Icc 0 2) : q t = t := by
              dsimp [q]
              rw [min_eq_left (by linarith [ht.2] : t ≤ 8-2*t), min_eq_right ht.2, max_eq_right ht.1]
            have qmiddle (r : ℝ) (hr0 : 2 ≤ r) (hr1 : r ≤ 3) : q r = 2 := by
              dsimp [q]
              rw [min_eq_left (le_min hr0 (by linarith)), max_eq_right (by norm_num)]
            have qhigh (r : ℝ) (hr : 4 ≤ r) : q r = 0 := by
              dsimp [q]
              apply max_eq_left
              exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))
            refine ⟨ψ, ?_, ?_⟩
            · intro x y hxy
              cases hxy with
              | a t i =>
                have hi : (i : ℝ) = 0 := by
                  have hz : i.val = 0 := by omega
                  exact_mod_cast hz
                have ht0 := t.property.1
                have ht1 := t.property.2
                simp only [Nat.cast_one,hi,mul_zero,zero_add,mul_one]
                change ∃ k : ℤ,
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((t:ℝ)/N)) -
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((1+(t:ℝ))/N)) = (k:ℝ)
                rw [value _ ht0 (by linarith),value _ (by linarith) (by linarith),
                  qlow _ ⟨ht0,by linarith⟩,qlow _ ⟨by linarith,by linarith⟩]
                exact ⟨-1,by ring⟩
              | c t i =>
                have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
                have hi0 : (0 : ℝ) ≤ i := by positivity
                have ht0 := t.property.1
                have ht1 := t.property.2
                simp only [Nat.cast_one,mul_one]
                change ∃ k : ℤ,
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+(t:ℝ))/N)) -
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+3-(t:ℝ))/N)) = (k:ℝ)
                rw [valueNeg _ (by linarith) (by dsimp [N]; linarith),
                    valueNeg _ (by linarith) (by dsimp [N]; linarith)]
                by_cases hz : i.val+1 = n
                · have hi' : (i : ℝ)+1 = n := by exact_mod_cast hz
                  rw [qhigh _ (by dsimp [N]; linarith),
                    qmiddle _ (by dsimp [N]; linarith) (by dsimp [N]; linarith)]
                  exact ⟨-2,by norm_num⟩
                · have hi' : (i : ℝ)+2 ≤ n := by exact_mod_cast (show i.val+2 ≤ n by omega)
                  rw [qhigh _ (by dsimp [N]; linarith),qhigh _ (by dsimp [N]; linarith)]
                  exact ⟨0,by simp⟩
            · intro t ht
              change ψ (Complex.ClosedUnitDisc.bdyPtOfReal (t/N)) = t
              rw [value t ht.1 (by linarith [ht.2]),qlow t ⟨ht.1,by linarith [ht.2]⟩]
          have construct {X : Type} [TopologicalSpace X] (R : X → X → Prop)
              (φ : C(X,ℝ))
              (hφ : ∀ x y, R x y → ∃ k : ℤ, φ x - φ y = (k : ℝ))
              (σ : ℝ → X) (hσ : ContinuousOn σ (Icc 0 1))
              (hends : Quot.mk R (σ 0) = Quot.mk R (σ 1))
              (hphase : ∀ t ∈ Icc (0 : ℝ) 1, φ (σ t) = t) :
              ∃ f : C(Quot R,Circle), ∃ g : C(Circle,Quot R), ∀ z, f (g z) = z := by
            have construct (F : C(X,Circle)) (hF : ∀ x y, R x y → F x = F y)
                (hwind : ∀ t ∈ Icc (0 : ℝ) 1,
                  F (σ t) = AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
                    (t : AddCircle (1 : ℝ))) :
                ∃ f : C(Quot R,Circle), ∃ g : C(Circle,Quot R), ∀ z, f (g z) = z := by
              let f : C(Quot R,Circle) := ⟨Quot.lift F hF, continuous_quot_lift hF F.continuous⟩
              let q : ℝ → Quot R := fun t => Quot.mk R (σ t)
              have he : q 0 = q (0+1) := by
                simpa only [q, zero_add] using hends
              have hc : ContinuousOn q (Icc 0 (0+1)) := by
                simpa only [zero_add, q, Function.comp_def] using
                  (continuous_quot_mk (r := R)).comp_continuousOn hσ
              let a : C(AddCircle (1 : ℝ),Quot R) :=
                ⟨AddCircle.liftIco (1 : ℝ) 0 q, AddCircle.liftIco_continuous he hc⟩
              have ha (z : AddCircle (1 : ℝ)) : f (a z) = AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero z := by
                let t := AddCircle.equivIco (1 : ℝ) 0 z
                have ht : (t : ℝ) ∈ Ico (0 : ℝ) 1 := by simpa only [zero_add] using t.property
                have hz : ((t : ℝ) : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco
                rw [← hz]
                change Quot.lift F hF (AddCircle.liftIco (1 : ℝ) 0 q (t : ℝ)) = _
                rw [AddCircle.liftIco_coe_apply (by simpa only [zero_add] using ht)]
                exact hwind t ⟨ht.1,le_of_lt ht.2⟩
              let g : C(Circle,Quot R) := a.comp ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm,
                  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous⟩
              exact ⟨f,g,fun z => (ha _).trans ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply z)⟩
            let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
            let F : C(X,Circle) := ⟨fun x => H (φ x : AddCircle (1 : ℝ)),
              H.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp φ.continuous)⟩
            apply construct F
            · intro x y hxy
              apply congrArg H
              apply QuotientAddGroup.eq_iff_sub_mem.mpr
              obtain ⟨k,hk⟩ := hφ x y hxy
              apply AddSubgroup.mem_zmultiples_iff.mpr
              exact ⟨k, by simpa only [zsmul_eq_mul, mul_one] using hk.symm⟩
            · intro t ht
              change H (φ (σ t) : AddCircle (1 : ℝ)) = H (t : AddCircle (1 : ℝ))
              rw [hphase t ht]
          have obstruction {U : Type} [TopologicalSpace U] [SimplyConnectedSpace U]
              (f : U → Circle) (g : Circle → U) (hf : Continuous f) (hg : Continuous g)
              (hfg : Function.RightInverse g f) : False := by
            have circleObstruction : ¬ SimplyConnectedSpace Circle := by
              intro h
              letI : SimplyConnectedSpace Circle := h
              let G := AddSubgroup.zmultiples (2 * π)
              let e := Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
                (x := Circle.exp 0) ⟨0, rfl⟩
              let a : G := ⟨0, (AddSubgroup.zmultiples (2 * π)).zero_mem⟩
              let b : G := ⟨2 * π, AddSubgroup.mem_zmultiples (2 * π)⟩
              have hab : MulOpposite.op (Multiplicative.ofAdd a) =
                  MulOpposite.op (Multiplicative.ofAdd b) := by
                apply e.symm.injective
                exact Subsingleton.elim _ _
              have hv : (0 : ℝ) = 2 * π :=
                congrArg (fun z : (Multiplicative G)ᵐᵒᵖ => ((MulOpposite.unop z).toAdd : ℝ)) hab
              have := Real.pi_pos
              linarith
            have retract : SimplyConnectedSpace Circle := by
              have hcomp : f ∘ g = id := funext hfg
              letI : PathConnectedSpace Circle := hfg.surjective.pathConnectedSpace hf
              apply simply_connected_iff_paths_homotopic'.mpr
              refine ⟨inferInstance, ?_⟩
              intro x y p q
              have H := (SimplyConnectedSpace.paths_homotopic (p.map hg) (q.map hg)).map
                (⟨f,hf⟩ : C(U,Circle))
              change Path.Homotopic ((p.map hg).map hf) ((q.map hg).map hf) at H
              have H' := H.pathCast (hfg x).symm (hfg y).symm
              have hp : (((p.map hg).map hf).cast (hfg x).symm (hfg y).symm) = p := by
                ext t
                exact congrArg Subtype.val (hfg (p t))
              have hq : (((q.map hg).map hf).cast (hfg x).symm (hfg y).symm) = q := by
                ext t
                exact congrArg Subtype.val (hfg (q t))
              rwa [hp,hq] at H'
            exact circleObstruction retract
          intro h
          letI : SimplyConnectedSpace (Quot (NonOrientableRel 1 n)) := h
          obtain ⟨ψ,hψ,hphase⟩ := phase
          let R := NonOrientableRel 1 n
          let σ : ℝ → Complex.ClosedUnitDisc :=
            fun t => Complex.ClosedUnitDisc.bdyPtOfReal (t/(2+3*n))
          have hc : Continuous σ := by
            apply Continuous.subtype_mk
            exact continuous_subtype_val.comp
              (Real.continuous_fourierChar.comp (by fun_prop))
          let i : Fin 1 := ⟨0,by omega⟩
          have ha0 := Quot.sound (NonOrientableRel.a (p := 1) (n := n)
            (⟨0,by norm_num⟩ : Icc (0:ℝ) 1) i)
          norm_num [i] at ha0
          have he : Quot.mk R (σ 0) = Quot.mk R (σ 1) := by
            simpa [σ, R, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ha0
          obtain ⟨f,g,hfg⟩ := construct R ψ hψ σ hc.continuousOn he hphase
          exact obstruction f g f.continuous g.continuous hfg
        have hob (n : ℕ) (hn : 2 ≤ n) : ¬ SimplyConnectedSpace (Quot (OrientableRel 0 n)) := by
          have phase : ∃ ψ : C(Complex.ClosedUnitDisc,ℝ),
              (∀ x y, OrientableRel 0 n x y → ∃ k : ℤ, ψ x - ψ y = (k : ℝ)) ∧
              (∀ t ∈ Icc (0 : ℝ) 1,
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(1+t)/(3*n))) = t) := by
            have build (N peak start width slope : ℝ) (hstart : 0 ≤ start)
                (hend : width ≤ slope*N) :
                ∃ φ : C(Circle,ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
                  φ (Real.fourierChar t) = max 0 (min peak (min (N*t-start) (width-slope*N*t))) := by
              have build : ∃ φ : C(AddCircle (1 : ℝ),ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
                  φ (t : AddCircle (1 : ℝ)) = max 0 (min peak (min (N*t-start) (width-slope*N*t))) := by
                let u : ℝ → ℝ := fun t => max 0 (min peak (min (N*t-start) (width-slope*N*t)))
                have h0 : u 0 = 0 := by
                  apply max_eq_left
                  exact (min_le_right _ _).trans ((min_le_left _ _).trans
                    (by simpa only [mul_zero, zero_sub] using neg_nonpos.mpr hstart))
                have h1 : u 1 = 0 := by
                  apply max_eq_left
                  exact (min_le_right _ _).trans ((min_le_right _ _).trans
                    (by simpa only [mul_one] using sub_nonpos.mpr hend))
                have he : u 0 = u (0+1) := by simpa only [zero_add,h0,h1]
                have hc : Continuous u := by
                  dsimp [u]
                  fun_prop
                let φ : C(AddCircle (1 : ℝ),ℝ) :=
                  ⟨AddCircle.liftIco (1 : ℝ) 0 u, AddCircle.liftIco_continuous he hc.continuousOn⟩
                refine ⟨φ, ?_⟩
                intro t ht
                rcases lt_or_eq_of_le ht.2 with hlt | rfl
                · change AddCircle.liftIco (1 : ℝ) 0 u (t : AddCircle (1 : ℝ)) = u t
                  exact AddCircle.liftIco_coe_apply (by simpa only [zero_add, Set.mem_Ico] using And.intro ht.1 hlt)
                · have hz : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
                  rw [hz]
                  change AddCircle.liftIco (1 : ℝ) 0 u (0 : AddCircle (1 : ℝ)) = u 1
                  rw [← AddCircle.coe_zero, AddCircle.liftIco_coe_apply (by norm_num),h0,h1]
              obtain ⟨φ,hφ⟩ := build
              let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
              let ψ : C(Circle,ℝ) := φ.comp ⟨H.symm,H.symm.continuous⟩
              have hparam (t : ℝ) : H (t : AddCircle (1 : ℝ)) = Real.fourierChar t := by
                simp only [H, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
                  div_one, Real.fourierChar_apply']
              refine ⟨ψ, ?_⟩
              intro t ht
              change φ (H.symm (Real.fourierChar t)) = _
              rw [← hparam t, H.symm_apply_apply]
              exact hφ t ht
            have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
            let N : ℝ := 3*n
            have hN : 6 ≤ N := by dsimp [N]; linarith
            have hNpos : 0 < N := by linarith
            obtain ⟨φ,hφ⟩ := build N 1 1 5 1 (by norm_num) (by linarith)
            let φneg : C(Circle,ℝ) := φ.comp ⟨fun z => z⁻¹,continuous_inv⟩
            let e : Circle → Complex.ClosedUnitDisc := fun z => ⟨z, by simp⟩
            have hec : Continuous e := continuous_subtype_val.subtype_mk _
            have hei : Function.Injective e := by
              intro x y h
              exact Subtype.ext (congrArg (fun z : Complex.ClosedUnitDisc => (z : ℂ)) h)
            have he : IsClosedEmbedding e := hec.isClosedEmbedding hei
            obtain ⟨ψ,hψ⟩ := φneg.exists_extension he
            have agrees (z : Circle) : ψ (e z) = φneg z := congrArg (fun f : C(Circle,ℝ) => f z) hψ
            let q : ℝ → ℝ := fun r => max 0 (min 1 (min (r-1) (5-r)))
            have valueNeg (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
                ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-r/N)) = q r := by
              change ψ (e (Real.fourierChar (-r/N))) = q r
              rw [agrees]
              change φ ((Real.fourierChar (-r/N))⁻¹) = q r
              rw [neg_div,AddChar.map_neg_eq_inv,inv_inv]
              have ht : r/N ∈ Icc (0 : ℝ) 1 :=
                ⟨div_nonneg hr0 hNpos.le, (div_le_one hNpos).mpr hrN⟩
              rw [hφ _ ht]
              dsimp [q]
              rw [one_mul,mul_div_cancel₀ r hNpos.ne']
            have qlow (r : ℝ) (hr : r ≤ 1) : q r = 0 := by
              dsimp [q]
              apply max_eq_left
              exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
            have qmiddle (r : ℝ) (hr0 : 2 ≤ r) (hr1 : r ≤ 4) : q r = 1 := by
              dsimp [q]
              rw [min_eq_left (le_min (by linarith) (by linarith)),max_eq_right (by norm_num)]
            have qhigh (r : ℝ) (hr : 5 ≤ r) : q r = 0 := by
              dsimp [q]
              apply max_eq_left
              exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))
            have qwind (t : ℝ) (ht : t ∈ Icc 0 1) : q (1+t) = t := by
              dsimp [q]
              have hh : 1+t-1 = t := by ring
              rw [hh,min_eq_left (by linarith [ht.2] : t ≤ 5-(1+t)),
                min_eq_right ht.2,max_eq_right ht.1]
            refine ⟨ψ, ?_, ?_⟩
            · intro x y hxy
              cases hxy with
              | a t i => exact Fin.elim0 i
              | b t i => exact Fin.elim0 i
              | c t i =>
                have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
                have hi0 : (0 : ℝ) ≤ i := by positivity
                have ht0 := t.property.1
                have ht1 := t.property.2
                simp only [Nat.cast_zero,mul_zero,zero_add]
                change ∃ k : ℤ,
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+(t:ℝ))/N)) -
                  ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+3-(t:ℝ))/N)) = (k:ℝ)
                rw [valueNeg _ (by linarith) (by dsimp [N]; linarith),
                    valueNeg _ (by linarith) (by dsimp [N]; linarith)]
                by_cases hz : i.val = 0
                · have hi' : (i : ℝ) = 0 := by exact_mod_cast hz
                  rw [hi']; simp only [mul_zero,zero_add]
                  rw [qlow _ ht1,qmiddle _ (by linarith) (by linarith)]
                  exact ⟨-1,by norm_num⟩
                · by_cases hz1 : i.val = 1
                  · have hi' : (i : ℝ) = 1 := by exact_mod_cast hz1
                    rw [hi']; norm_num only [mul_one]
                    rw [qmiddle _ (by linarith) (by linarith),qhigh _ (by linarith)]
                    exact ⟨1,by norm_num⟩
                  · have hi' : (2 : ℝ) ≤ i := by exact_mod_cast (show 2 ≤ i.val by omega)
                    rw [qhigh _ (by linarith),qhigh _ (by linarith)]
                    exact ⟨0,by simp⟩
            · intro t ht
              change ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(1+t)/N)) = t
              rw [valueNeg _ (by linarith [ht.1]) (by linarith [ht.2]),qwind t ht]
          have construct {X : Type} [TopologicalSpace X] (R : X → X → Prop)
              (φ : C(X,ℝ))
              (hφ : ∀ x y, R x y → ∃ k : ℤ, φ x - φ y = (k : ℝ))
              (σ : ℝ → X) (hσ : ContinuousOn σ (Icc 0 1))
              (hends : Quot.mk R (σ 0) = Quot.mk R (σ 1))
              (hphase : ∀ t ∈ Icc (0 : ℝ) 1, φ (σ t) = t) :
              ∃ f : C(Quot R,Circle), ∃ g : C(Circle,Quot R), ∀ z, f (g z) = z := by
            have construct (F : C(X,Circle)) (hF : ∀ x y, R x y → F x = F y)
                (hwind : ∀ t ∈ Icc (0 : ℝ) 1,
                  F (σ t) = AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
                    (t : AddCircle (1 : ℝ))) :
                ∃ f : C(Quot R,Circle), ∃ g : C(Circle,Quot R), ∀ z, f (g z) = z := by
              let f : C(Quot R,Circle) := ⟨Quot.lift F hF, continuous_quot_lift hF F.continuous⟩
              let q : ℝ → Quot R := fun t => Quot.mk R (σ t)
              have he : q 0 = q (0+1) := by
                simpa only [q, zero_add] using hends
              have hc : ContinuousOn q (Icc 0 (0+1)) := by
                simpa only [zero_add, q, Function.comp_def] using
                  (continuous_quot_mk (r := R)).comp_continuousOn hσ
              let a : C(AddCircle (1 : ℝ),Quot R) :=
                ⟨AddCircle.liftIco (1 : ℝ) 0 q, AddCircle.liftIco_continuous he hc⟩
              have ha (z : AddCircle (1 : ℝ)) : f (a z) = AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero z := by
                let t := AddCircle.equivIco (1 : ℝ) 0 z
                have ht : (t : ℝ) ∈ Ico (0 : ℝ) 1 := by simpa only [zero_add] using t.property
                have hz : ((t : ℝ) : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco
                rw [← hz]
                change Quot.lift F hF (AddCircle.liftIco (1 : ℝ) 0 q (t : ℝ)) = _
                rw [AddCircle.liftIco_coe_apply (by simpa only [zero_add] using ht)]
                exact hwind t ⟨ht.1,le_of_lt ht.2⟩
              let g : C(Circle,Quot R) := a.comp ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm,
                  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous⟩
              exact ⟨f,g,fun z => (ha _).trans ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply z)⟩
            let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
            let F : C(X,Circle) := ⟨fun x => H (φ x : AddCircle (1 : ℝ)),
              H.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp φ.continuous)⟩
            apply construct F
            · intro x y hxy
              apply congrArg H
              apply QuotientAddGroup.eq_iff_sub_mem.mpr
              obtain ⟨k,hk⟩ := hφ x y hxy
              apply AddSubgroup.mem_zmultiples_iff.mpr
              exact ⟨k, by simpa only [zsmul_eq_mul, mul_one] using hk.symm⟩
            · intro t ht
              change H (φ (σ t) : AddCircle (1 : ℝ)) = H (t : AddCircle (1 : ℝ))
              rw [hphase t ht]
          have obstruction {U : Type} [TopologicalSpace U] [SimplyConnectedSpace U]
              (f : U → Circle) (g : Circle → U) (hf : Continuous f) (hg : Continuous g)
              (hfg : Function.RightInverse g f) : False := by
            have circleObstruction : ¬ SimplyConnectedSpace Circle := by
              intro h
              letI : SimplyConnectedSpace Circle := h
              let G := AddSubgroup.zmultiples (2 * π)
              let e := Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
                (x := Circle.exp 0) ⟨0, rfl⟩
              let a : G := ⟨0, (AddSubgroup.zmultiples (2 * π)).zero_mem⟩
              let b : G := ⟨2 * π, AddSubgroup.mem_zmultiples (2 * π)⟩
              have hab : MulOpposite.op (Multiplicative.ofAdd a) =
                  MulOpposite.op (Multiplicative.ofAdd b) := by
                apply e.symm.injective
                exact Subsingleton.elim _ _
              have hv : (0 : ℝ) = 2 * π :=
                congrArg (fun z : (Multiplicative G)ᵐᵒᵖ => ((MulOpposite.unop z).toAdd : ℝ)) hab
              have := Real.pi_pos
              linarith
            have retract : SimplyConnectedSpace Circle := by
              have hcomp : f ∘ g = id := funext hfg
              letI : PathConnectedSpace Circle := hfg.surjective.pathConnectedSpace hf
              apply simply_connected_iff_paths_homotopic'.mpr
              refine ⟨inferInstance, ?_⟩
              intro x y p q
              have H := (SimplyConnectedSpace.paths_homotopic (p.map hg) (q.map hg)).map
                (⟨f,hf⟩ : C(U,Circle))
              change Path.Homotopic ((p.map hg).map hf) ((q.map hg).map hf) at H
              have H' := H.pathCast (hfg x).symm (hfg y).symm
              have hp : (((p.map hg).map hf).cast (hfg x).symm (hfg y).symm) = p := by
                ext t
                exact congrArg Subtype.val (hfg (p t))
              have hq : (((q.map hg).map hf).cast (hfg x).symm (hfg y).symm) = q := by
                ext t
                exact congrArg Subtype.val (hfg (q t))
              rwa [hp,hq] at H'
            exact circleObstruction retract
          intro h
          letI : SimplyConnectedSpace (Quot (OrientableRel 0 n)) := h
          obtain ⟨ψ,hψ,hphase⟩ := phase
          let R := OrientableRel 0 n
          let σ : ℝ → Complex.ClosedUnitDisc :=
            fun t => Complex.ClosedUnitDisc.bdyPtOfReal (-(1+t)/(3*n))
          have hc : Continuous σ := by
            apply Continuous.subtype_mk
            exact continuous_subtype_val.comp
              (Real.continuous_fourierChar.comp (by fun_prop))
          let i : Fin n := ⟨0,by omega⟩
          have hc1 := Quot.sound (OrientableRel.c (p := 0) (n := n)
            (⟨1,by norm_num⟩ : Icc (0:ℝ) 1) i)
          norm_num [i] at hc1
          have he : Quot.mk R (σ 0) = Quot.mk R (σ 1) := by
            convert hc1 using 1 <;> simp [σ, R, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] <;>
              congr 1 <;> ring
          obtain ⟨f,g,hfg⟩ := construct R ψ hψ σ hc.continuousOn he hphase
          exact obstruction f g f.continuous g.continuous hfg
        have classify : Nonempty (U ≃ₜ SphereRepresentative) ∨
            ∃ p n, ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (U ≃ₜ Quot (OrientableRel p n))) ∨
              (1 ≤ p ∧ Nonempty (U ≃ₜ Quot (NonOrientableRel p n))) := by
          have adapter : Nonempty (ChartedSpace (EuclideanHalfSpace 2) U) := by
            let P := EuclideanSpace ℝ (Fin 2)
            let h : P ≃ₜ ℝ × ℝ :=
              (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow (X := ℝ))
            let e : OpenPartialHomeomorph P P := h.toOpenPartialHomeomorph.trans
              ((Real.expPartialHomeomorph.prod (OpenPartialHomeomorph.refl ℝ)).trans
                h.symm.toOpenPartialHomeomorph)
            have es : e.source = univ := by simp [e]
            have et : e.target = {x : P | 0 < x 0} := by
              ext x
              simp [e, h, Homeomorph.finTwoArrow, Real.expPartialHomeomorph]
              rfl
            have ep (x : P) : 0 < e x 0 := by
              have hh := e.map_source (show x ∈ e.source by rw [es]; trivial)
              rwa [et] at hh
            let a : OpenPartialHomeomorph P (EuclideanHalfSpace 2) := {
              toFun := fun x => ⟨e x, le_of_lt (ep x)⟩
              invFun := fun y => e.symm y.val
              source := univ
              target := {y | 0 < y.val 0}
              map_source' := fun x _ => ep x
              map_target' := fun _ _ => mem_univ _
              left_inv' := fun x _ => e.left_inv (by rw [es]; trivial)
              right_inv' := by
                intro y hy
                apply Subtype.ext
                exact e.right_inv (by rwa [et])
              open_source := isOpen_univ
              open_target := isOpen_lt continuous_const
                (((continuous_apply 0).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous).comp continuous_subtype_val)
              continuousOn_toFun := by
                apply Continuous.continuousOn
                exact (continuousOn_univ.mp (by simpa only [es] using e.continuousOn)).subtype_mk _
              continuousOn_invFun := by
                apply e.symm.continuousOn.comp continuous_subtype_val.continuousOn
                intro y hy
                rwa [e.symm_source, et]
            }
            letI : ChartedSpace (EuclideanHalfSpace 2) P := {
              atlas := {a}
              chartAt := fun _ => a
              mem_chart_source := fun _ => mem_univ _
              chart_mem_atlas := fun _ => mem_singleton _
            }
            exact ⟨ChartedSpace.comp (EuclideanHalfSpace 2) P U⟩
          letI : ChartedSpace (EuclideanHalfSpace 2) U := adapter.some
          exact classification_of_surfaces U
        rcases classify with hSphere | ⟨p,n,h⟩
        · obtain ⟨h⟩ := hSphere
          exact Or.inl ⟨h.symm⟩
        · rcases h with ⟨hadm,⟨h⟩⟩ | ⟨hp,⟨h⟩⟩
          · letI : SimplyConnectedSpace (Quot (OrientableRel p n)) :=
              h.symm.toHomotopyEquiv.simplyConnectedSpace
            by_cases hp : 1 ≤ p
            · exact False.elim (ho p n hp inferInstance)
            · have hp0 : p = 0 := by omega
              subst p
              have hn1 : 1 ≤ n := by omega
              by_cases hn2 : 2 ≤ n
              · exact False.elim (hob n hn2 inferInstance)
              · have hn : n = 1 := by omega
                subst n
                exact Or.inr (Or.inl ⟨h.symm⟩)
          · letI : SimplyConnectedSpace (Quot (NonOrientableRel p n)) :=
              h.symm.toHomotopyEquiv.simplyConnectedSpace
            by_cases hp2 : 2 ≤ p
            · exact False.elim (hn p n hp2 inferInstance)
            · have hp1 : p = 1 := by omega
              subst p
              by_cases hn1 : 1 ≤ n
              · exact False.elim (hnb n hn1 inferInstance)
              · have hn0 : n = 0 := by omega
                subst n
                exact Or.inr (Or.inr ⟨h.symm⟩)
      have disk : Nonempty ((Quot (OrientableRel 0 1)) ≃ₜ Complex.ClosedUnitDisc) := by
        have monogon (valid : (Dyck.oneFace ([.pos 0] : List (SignedDart (Fin 1)))).IsSurfaceValid) :
            Nonempty ((Dyck.oneFace ([.pos 0] : List (SignedDart (Fin 1)))).PolygonalRealization valid ≃ₜ
              Complex.ClosedUnitDisc) := by
          let P := Dyck.oneFace ([.pos 0] : List (SignedDart (Fin 1)))
          have hf (f : P.Face) : f = 0 := by
            apply Fin.ext
            have h := f.isLt
            change f.val < 1 at h
            change f.val = 0
            omega
          have hb (f : P.Face) : (P.boundary f).length = 1 := by rw [hf f]; rfl
          have hi : P.polygonalIdentifications valid = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            rintro x ⟨b,rfl⟩
            have ho (o : P.BoundaryOccurrence) : o = ⟨0,⟨0,by rw [hb]; norm_num⟩⟩ := by
              obtain ⟨f,i⟩ := o
              have hh := hf f
              subst f
              have hh : i = ⟨0,by rw [hb]; norm_num⟩ := by
                apply Fin.ext
                have h := i.isLt
                change i.val < 1 at h
                change i.val = 0
                omega
              subst i
              rfl
            exact b.source_ne_target ((ho b.source).trans (ho b.target).symm)
          let d : P.PolygonalPreRealization ≃ₜ Complex.ClosedUnitDisc := {
            toFun := fun x => ⟨x.2.val,x.2.property⟩
            invFun := fun x => ⟨0,⟨x.val,x.property⟩⟩
            left_inv := by
              intro x
              obtain ⟨f,x⟩ := x
              have h := hf f
              subst f
              rfl
            right_inv := by intro x; rfl
            continuous_toFun := by
              apply continuous_sigma
              intro f
              exact PolygonCell.continuous_val.subtype_mk _
            continuous_invFun := by
              exact continuous_sigmaMk.comp (continuous_induced_rng.mpr continuous_subtype_val)
          }
          exact ⟨(Homeomorph.Quotient.congrRight (by
            intro x y
            change PolygonGluing.setoid (P.polygonalIdentifications valid) x y ↔ (⊥ : Setoid P.PolygonalPreRealization) x y
            rw [hi,PolygonGluing.setoid_empty])).trans (Homeomorph.quotientBot.trans d)⟩
        let word : List (SignedDart (Fin 2)) := [.pos 0,.pos 1,.neg 0]
        let e : Fin 2 ≃ NormalForm.OrientableEdge 0 1 := {
          toFun := fun i => if i = 0 then .c 0 else .h 0
          invFun := fun x => match x with
            | .a i => Fin.elim0 i
            | .b i => Fin.elim0 i
            | .c _ => 0
            | .h _ => 1
          left_inv := by intro i; fin_cases i <;> simp
          right_inv := by
            intro x
            cases x with
            | a i => exact Fin.elim0 i
            | b i => exact Fin.elim0 i
            | c i => have h : i = 0 := Subsingleton.elim _ _; subst i; rfl
            | h i => have h : i = 0 := Subsingleton.elim _ _; subst i; rfl
        }
        have hw : (word.map (SignedDart.mapEquiv e)).IsRotated
            (NormalForm.orientableBoundaryWord 0 1) := by
          have heq : word.map (SignedDart.mapEquiv e) = NormalForm.orientableBoundaryWord 0 1 := by
            simp [word,e,SignedDart.mapEquiv,NormalForm.orientableBoundaryWord,
              NormalForm.orientableBoundaryBlock,List.ofFn_succ]
          rw [heq]
        let iso := WordReduction.oneFaceSignedIsoToOfOneFaceWord word
          (NormalForm.orientableBoundaryWord 0 1) e hw
        let vc := NormalForm.canonicalPresentation_isSurfaceValid (.orientable 0 1)
          (show 1 ≤ 0 ∨ 1 ≤ 1 from Or.inr le_rfl)
        let vs : (Dyck.oneFace word).IsSurfaceValid := iso.symm.isSurfaceValid vc
        have hr : word.IsRotated ([.neg (0 : Fin 2),.pos 0] ++ [.pos 1]) := by
          exact ⟨2,by decide⟩
        have ha : (0 : Fin 2) ∉ ([.pos 1] : List (SignedDart (Fin 2))).map edgeOfDart := by decide
        have hl : Cancellation.lowerTail (0 : Fin 2) ([.pos 1] : List (SignedDart (Fin 2))) =
            ([.pos 0] : List (SignedDart (Fin 1))) := by decide
        have hc := Cancellation.negativeNormalizationEquivalentOfIsRotated word 0 [.pos 1] hr ha
          (by rw [hl]; simp) vs
        obtain ⟨h⟩ := hc.polygonallyEquivalent
        simp only [Cancellation.target,hl] at h
        exact ⟨(NormalForm.canonicalOrientableRealizationHomeomorph (p := 0) (n := 1)
          (Or.inr le_rfl)).symm.trans ((iso.realizationHomeomorph vs vc).symm.trans
            (h.trans (Classical.choice (monogon _))))⟩
      have notDisc {U : Type} [TopologicalSpace U]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U] :
          ¬ Nonempty (Complex.ClosedUnitDisc ≃ₜ U) := by
        rintro ⟨e⟩
        let K := closedBall (0 : Plane) 1
        let d : Complex.ClosedUnitDisc ≃ₜ K := complexLIE.toHomeomorph.subtype (by
          intro z
          change z ∈ closedBall (0 : ℂ) 1 ↔ complexLIE z ∈ closedBall (0 : Plane) 1
          simp only [mem_closedBall,dist_zero_right,LinearIsometryEquiv.norm_map])
        let f : K ≃ₜ U := d.symm.trans e
        let x : K := d ⟨1,by norm_num [mem_closedBall]⟩
        have hr : range f = univ := f.surjective.range_eq
        have hx : f x ∈ interior (range f) := by rw [hr,interior_univ]; trivial
        have hi := (CurveComplex.embedded_planar_region_interior_iff_probe K f f.isEmbedding x).mp hx
        have hn : ‖(x : Plane)‖ = 1 := by
          change ‖complexLIE (1 : ℂ)‖ = 1
          simp
        rw [show interior K = ball (0 : Plane) 1 from interior_closedBall _ one_ne_zero] at hi
        simpa only [mem_ball,dist_zero_right,hn,lt_self_iff_false] using hi
      rcases three (U := U) with hs | hd | hp
      · exact Or.inl hs
      · obtain ⟨h⟩ := hd
        obtain ⟨d⟩ := disk
        exact False.elim (notDisc (U := U) ⟨d.symm.trans h⟩)
      · exact Or.inr hp
    rcases compactModels (U := U) with hSphere | hProjective
    · exact Or.inr hSphere
    · obtain ⟨eProjective⟩ := hProjective
      have actualAntipodalCover : ∃ action : MulAction ℤˣ SphereRepresentative,
          letI := action
          (∀ (v : ℤˣ) (x : SphereRepresentative), (v • x).val = v.val • x.val) ∧
          IsCoveringMap (Quotient.mk (MulAction.orbitRel ℤˣ SphereRepresentative)) ∧
          ¬ Function.Injective (Quotient.mk (MulAction.orbitRel ℤˣ SphereRepresentative)) := by
        letI : MulAction ℤˣ SphereRepresentative := {
          smul := fun u x => ⟨u.val • x,by
            rcases Int.units_eq_one_or u with hu | hu
            · subst u
              simpa only [Units.val_one,one_zsmul] using x.property
            · subst u
              simpa only [Units.val_neg,Units.val_one,neg_one_zsmul,Metric.mem_sphere,
                dist_zero_right,norm_neg] using x.property⟩
          one_smul := by intro x; apply Subtype.ext; exact one_smul _ _
          mul_smul := by intro u v x; apply Subtype.ext; exact mul_smul _ _ _
        }
        have nofix (x : SphereRepresentative) : -x.val ≠ x.val := by
          intro h
          have hz : x.val = 0 := by
            ext i
            have hi := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z i) h
            simp only [PiLp.neg_apply,PiLp.zero_apply] at hi ⊢
            linarith
          have hn := x.property
          rw [mem_sphere_zero_iff_norm,hz,norm_zero] at hn
          norm_num at hn
        letI : ContinuousConstSMul ℤˣ SphereRepresentative := ⟨fun u =>
          ((continuous_const_smul u).comp continuous_subtype_val).subtype_mk _⟩
        letI : ProperlyDiscontinuousSMul ℤˣ SphereRepresentative := ⟨fun _ _ => Set.toFinite _⟩
        letI : IsCancelSMul ℤˣ SphereRepresentative :=
          isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
            intro u x hx
            have hu : u = 1 ∨ u = -1 := by
              have hi := u.val_inv
              rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hi with h | h
              · left; apply Units.ext; exact h.1
              · right; apply Units.ext; exact h.1
            rcases hu with rfl | rfl
            · rfl
            · exfalso
              apply nofix x
              have hv := congrArg Subtype.val hx
              change (-1 : ℤˣ) • x.val = x.val at hv
              simpa only [Units.smul_def,Units.val_neg,Units.val_one,neg_one_zsmul] using hv)
        refine ⟨inferInstance,(fun _ _ => rfl),
          isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap,?_⟩
        intro hinj
        let x : SphereRepresentative := PolygonCell.upperHemisphere
          (⟨0,by simp⟩ : PolygonCell 1)
        have hq : Quotient.mk (MulAction.orbitRel ℤˣ SphereRepresentative) ((-1 : ℤˣ) • x) =
            Quotient.mk (MulAction.orbitRel ℤˣ SphereRepresentative) x := Quotient.sound ⟨-1,rfl⟩
        have hx := congrArg Subtype.val (hinj hq)
        change (-1 : ℤˣ) • x.val = x.val at hx
        exact nofix x (by simpa only [Units.smul_def,Units.val_neg,Units.val_one,neg_one_zsmul] using hx)
      obtain ⟨action,hAction,hDoubleCover,hNoninjective⟩ := actualAntipodalCover
      letI := action
      let Q := Quotient (MulAction.orbitRel ℤˣ SphereRepresentative)
      have hProjectiveModel : Nonempty ((Quot (NonOrientableRel 1 0)) ≃ₜ Q) := by
        exact original_projective_plane_disk_antipodal_orbit_homeomorphism action hAction
      obtain ⟨eAntipodal⟩ := hProjectiveModel
      let eU : U ≃ₜ Q := eProjective.symm.trans eAntipodal
      letI : SimplyConnectedSpace Q :=
        eU.toHomotopyEquiv.simplyConnectedSpace_iff.mp inferInstance
      letI : LocallyPathConnectedSpace Q := eU.isQuotientMap.locallyPathConnectedSpace
      letI : ConnectedSpace SphereRepresentative := Subtype.connectedSpace
        (isConnected_sphere (by
          apply Module.one_lt_rank_of_one_lt_finrank
          simp) (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num))
      have injectiveCover {E X : Type} [TopologicalSpace E] [PreconnectedSpace E]
          [TopologicalSpace X] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
          (p : E → X) (hp : IsCoveringMap p) : Function.Injective p := by
        intro a b hab
        obtain ⟨g,⟨hga,hg⟩,_⟩ := hp.existsUnique_continuousMap_lifts
          (ContinuousMap.id X) (p a) a rfl
        have he : p ∘ (g ∘ p) = p ∘ id := by
          ext e
          exact congrFun hg (p e)
        have ha : (g ∘ p) a = id a := hga
        have hi := hp.eq_of_comp_eq (g.continuous.comp hp.continuous) continuous_id he a ha
        calc
          a = g (p a) := (congrFun hi a).symm
          _ = g (p b) := congrArg g hab
          _ = b := congrFun hi b
      exact False.elim (hNoninjective (injectiveCover _ hDoubleCover))
  · have hActualGenusZeroNeighborhood : ∀ K : Set U, IsCompact K →
        ∃ N : Set U, IsCompact N ∧ K ⊆ interior N ∧ IsConnected (interior N) ∧ closure (interior N)=N ∧
          (∃ n : ℕ, 1 ≤ n ∧ Nonempty (N ≃ₜ Quot (OrientableRel 0 n))) ∧
          ∃ J : Set U, IsCompact J ∧ N ⊆ J ∧
            ∀ z ∈ frontier N, ∃ c : CurveComplex.Curve U,
              z ∈ c.image ∧ c.image ⊆ frontier N ∧ c.image ⊆ Kᶜ ∧
              ∃ y : U, ∃ H : ContinuousMap.Homotopy
                (⟨c.map,c.embedded.continuous⟩ : C(Circle,U))
                (ContinuousMap.const Circle y), Set.range H ⊆ J ∧ ∃ V : Set U, IsOpen V ∧ c.image ⊆ V ∧
                  ∀ z ∈ V, z ∈ frontier N ↔ z ∈ c.image := by
      intro K hK
      have actualCutCover (a : Curve U) : Nonempty (CurveCutCover a) := by
        classical
        let C (p : a.image) : OpenPartialHomeomorph U (ℝ × ℝ) := by
          let H := actual_surface_embedded_curve_has_local_axis_chart a p p.property
          let axisDomain := H.choose
          let V := H.choose_spec.choose
          let hp := H.choose_spec.choose_spec.choose
          let h := H.choose_spec.choose_spec.choose_spec.choose
          let spec := H.choose_spec.choose_spec.choose_spec.choose_spec
          exact crossingPartialChart axisDomain V spec.1 spec.2.1 ⟨p,hp⟩ h
        let D : Option a.image → Set U
          | none => a.imageᶜ
          | some p => (C p).source
        let indexAt (x : U) : Option a.image :=
          if hx : x ∈ a.image then some ⟨x,hx⟩ else none
        let label : Option a.image → U → ZMod 2
          | none,_ => 0
          | some p,x => if 0 < (C p x).1 then 1 else 0
        have hchart (p : a.image) : p.val ∈ (C p).source ∧ C p p.val = (0, 0) ∧
            ∀ x ∈ (C p).source, x ∈ a.image ↔ (C p x).1 = 0 := by
          let H := actual_surface_embedded_curve_has_local_axis_chart a p p.property
          let axisDomain := H.choose
          let V := H.choose_spec.choose
          let hp := H.choose_spec.choose_spec.choose
          let h := H.choose_spec.choose_spec.choose_spec.choose
          let spec := H.choose_spec.choose_spec.choose_spec.choose_spec
          have hCs : (C p).source = axisDomain := by simp [C, H, axisDomain, V, hp, h, crossingPartialChart]
          have hval (x : U) (hx : x ∈ axisDomain) : C p x = (h ⟨x, hx⟩ : ℝ × ℝ) := by
            change crossingPartialChart axisDomain V spec.1 spec.2.1 ⟨p, hp⟩ h x = _
            simp only [crossingPartialChart, OpenPartialHomeomorph.trans_apply,
              Homeomorph.toOpenPartialHomeomorph_apply]
            change (h (((⟨axisDomain, spec.1⟩ : TopologicalSpace.Opens U).openPartialHomeomorphSubtypeCoe
              ⟨⟨p, hp⟩⟩).symm x) : ℝ × ℝ) = (h ⟨x, hx⟩ : ℝ × ℝ)
            have hinv := ((⟨axisDomain, spec.1⟩ : TopologicalSpace.Opens U).openPartialHomeomorphSubtypeCoe
              ⟨⟨p, hp⟩⟩).left_inv (show (⟨x, hx⟩ : axisDomain) ∈ Set.univ from trivial)
            change ((⟨axisDomain, spec.1⟩ : TopologicalSpace.Opens U).openPartialHomeomorphSubtypeCoe
              ⟨⟨p, hp⟩⟩).symm x = ⟨x, hx⟩ at hinv
            rw [hinv]
          refine ⟨hCs.symm ▸ hp, (hval p hp).trans spec.2.2.1, ?_⟩
          intro x hx
          rw [hval x (hCs ▸ hx)]
          have hxU : x ∈ axisDomain := hCs ▸ hx
          exact spec.2.2.2 x hxU
        have hclosed : IsClosed a.image := by
          simpa [Curve.image, Set.image_univ] using (isCompact_univ.image a.embedded.continuous).isClosed
        have hDopen : ∀ i, IsOpen (D i) := by
          intro i
          cases i with
          | none => exact hclosed.isOpen_compl
          | some p => exact (C p).open_source
        have hDmem : ∀ x, x ∈ D (indexAt x) := by
          intro x
          by_cases hx : x ∈ a.image
          · simpa [indexAt, D, hx] using (hchart ⟨x, hx⟩).1
          · simpa [indexAt, D, hx] using hx
        have hlabelcont : ∀ i, ContinuousOn (label i) (D i ∩ a.imageᶜ) := by
          intro i
          cases i with
          | none => exact continuousOn_const
          | some p =>
            intro x hx
            have hn : (C p x).1 ≠ 0 := fun hz => hx.2 ((hchart p).2.2 x hx.1 |>.mpr hz)
            have hc := continuous_fst.continuousAt.comp ((C p).continuousAt hx.1)
            have he : (label (some p)) =ᶠ[𝓝 x] fun _ => label (some p) x := by
              by_cases hpos : 0 < (C p x).1
              · filter_upwards [hc.preimage_mem_nhds (Ioi_mem_nhds hpos)] with y hy
                change 0 < (C p y).1 at hy
                simp [label, hpos, hy]
              · have hneg : (C p x).1 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hn
                filter_upwards [hc.preimage_mem_nhds (Iio_mem_nhds hneg)] with y hy
                change (C p y).1 < 0 at hy
                simp [label, hpos, not_lt_of_ge hy.le]
            exact he.continuousAt.continuousWithinAt
        have hchanges : ∀ i j : Option a.image, ∃ τ : U → ZMod 2,
            ContinuousOn τ (D i ∩ D j) ∧
            ∀ x ∈ D i ∩ D j, x ∉ a.image → τ x = label i x + label j x := by
          intro i j
          cases i with
          | none =>
            cases j with
            | none => exact ⟨fun _ => 0, continuousOn_const, by intros; simp [label]⟩
            | some q =>
              refine ⟨label (some q), (hlabelcont (some q)).mono (fun x hx => ⟨hx.2, hx.1⟩), ?_⟩
              intros
              simp [label]
          | some p =>
            cases j with
            | none =>
              refine ⟨label (some p), (hlabelcont (some p)).mono (fun _ hx => hx), ?_⟩
              intros
              simp [label]
            | some q =>
              exact axis_chart_relative_side_extension a.image (C p) (C q)
                (hchart p).2.2 (hchart q).2.2
        let τ := fun i j => (hchanges i j).choose
        have hτcont (i j) : ContinuousOn (τ i j) (D i ∩ D j) := (hchanges i j).choose_spec.1
        have hτval (i j) (x : U) (hx : x ∈ D i ∩ D j) (hxa : x ∉ a.image) :
            τ i j x = label i x + label j x := (hchanges i j).choose_spec.2 x hx hxa
        have hdense (i : Option a.image) (W : Set U) (hW : IsOpen W) (hWi : W ⊆ D i) :
            Dense {x : W | (x : U) ∉ a.image} := by
          cases i with
          | none =>
            have heq : {x : W | (x : U) ∉ a.image} = Set.univ := by
              ext x
              simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
              exact hWi x.property
            rw [heq]
            exact dense_univ
          | some p => exact axis_chart_complement_dense a.image (C p) (hchart p).2.2 W hW hWi
        have huniq (i : Option a.image) (W : Set U) (hW : IsOpen W) (hWi : W ⊆ D i)
            (f g : U → ZMod 2) (hf : ContinuousOn f W) (hg : ContinuousOn g W)
            (heq : ∀ x ∈ W, x ∉ a.image → f x = g x) : Set.EqOn f g W := by
          have hden := (hdense i W hW hWi).denseRange_val
          have heq' : W.domRestrict f = W.domRestrict g := hden.equalizer
            (continuousOn_iff_continuous_restrict.mp hf)
            (continuousOn_iff_continuous_restrict.mp hg)
            (funext fun x => heq x.val.val x.val.property x.property)
          intro x hx
          exact congrFun heq' ⟨x, hx⟩
        have hself : ∀ i x, x ∈ D i → τ i i x = 0 := by
          intro i
          apply huniq i (D i) (hDopen i) (fun _ hx => hx) (τ i i) (fun _ => 0)
            (by simpa only [Set.inter_self] using hτcont i i) continuousOn_const
          intro x hx hxa
          rw [hτval i i x ⟨hx, hx⟩ hxa, CharTwo.add_self_eq_zero]
        have hAdd : Continuous (fun q : ZMod 2 × ZMod 2 => q.1 + q.2) := continuous_of_discreteTopology
        have hcocycle : ∀ i j k x, x ∈ D i ∩ D j ∩ D k →
            τ i j x + τ j k x = τ i k x := by
          intro i j k
          apply huniq i (D i ∩ D j ∩ D k) ((hDopen i).inter (hDopen j) |>.inter (hDopen k))
            (fun _ hx => hx.1.1) (fun x => τ i j x + τ j k x) (τ i k)
            (hAdd.comp_continuousOn (((hτcont i j).mono fun _ hx => hx.1).prodMk
              ((hτcont j k).mono fun _ hx => ⟨hx.1.2, hx.2⟩)))
            ((hτcont i k).mono fun _ hx => ⟨hx.1.1, hx.2⟩)
          intro x hx hxa
          rw [hτval i j x hx.1 hxa, hτval j k x ⟨hx.1.2, hx.2⟩ hxa,
            hτval i k x ⟨hx.1.1, hx.2⟩ hxa]
          rw [add_assoc, ← add_assoc (label j x), CharTwo.add_self_eq_zero, zero_add]
        let atlas : TwoSheetCocycle (Option a.image) U :=
          ⟨D, hDopen, indexAt, hDmem, τ, hτcont, hself, hcocycle⟩
        let core := atlas.bundleCore
        refine ⟨{
          core := core
          complementTriv := core.localTriv none
          complement_baseSet := rfl
          localCut := ?_ }⟩
        intro p hp
        let q : a.image := ⟨p, hp⟩
        refine ⟨C q, (hchart q).1, (hchart q).2.1, (hchart q).2.2,
          core.localTriv (some q), rfl, ?_⟩
        intro z hz hzoff
        have hidx := hDmem z.proj
        have hco := hcocycle (indexAt z.proj) (some q) none z.proj ⟨⟨hidx, hz⟩, hzoff⟩
        have hlast := hτval (some q) none z.proj ⟨hz, hzoff⟩ hzoff
        change τ (some q) none z.proj =
          (if 0 < (C q z.proj).1 then 1 else 0) + 0 at hlast
        rw [add_zero] at hlast
        rw [FiberBundleCore.localTriv_apply, FiberBundleCore.localTriv_apply]
        change (show ZMod 2 from z.snd) + τ (indexAt z.proj) none z.proj =
          ((show ZMod 2 from z.snd) + τ (indexAt z.proj) (some q) z.proj) +
            (if 0 < (C q z.proj).1 then 1 else 0)
        rw [← hco, hlast, add_assoc]
      have actualTransverseParity (a b : Curve U) (hab : Transverse a b) :
          Even hab.1.toFinset.card := by
        obtain ⟨A⟩ := actualCutCover a
        classical
        have hfinite : {z : Circle | b.map z ∈ a.image}.Finite := by
          have hpre := hab.1.preimage b.embedded.injective.injOn
          have hset : b.map ⁻¹' (a.image ∩ b.image) = {z | b.map z ∈ a.image} := by
            ext z
            simp only [Set.mem_preimage,Set.mem_inter_iff,Set.mem_ofPred_eq]
            exact and_iff_left ⟨z,rfl⟩
          rwa [hset] at hpre
        have hbase : ∃ z : Circle, b.map z ∉ a.image := by
          by_contra h
          push Not at h
          have hwhole : {z : Circle | b.map z ∈ a.image} = Set.univ := Set.eq_univ_of_forall h
          have hfin : (Set.univ : Set Circle).Finite := hwhole ▸ hfinite
          letI : Finite Circle := Set.finite_univ_iff.mp hfin
          letI : DiscreteTopology Circle := inferInstance
          letI : Subsingleton Circle := subsingleton_of_preconnected_totallyDisconnected
          have hcontra := congrArg Subtype.val
            (Subsingleton.elim (1 : Circle)
              (⟨(-1 : ℂ),by change dist (-1 : ℂ) 0 = 1; simp [dist_eq_norm]⟩ : Circle))
          norm_num at hcontra
        obtain ⟨z,hz⟩ := hbase
        letI : LocallyPathConnectedSpace U :=
          ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) U
        have cov : IsCoveringMap A.core.proj :=
          FiberBundle.isCoveringMap (F := ZMod 2) (E := A.core.Fiber)
        let start : A.core.TotalSpace := ⟨b.map z,(0 : ZMod 2)⟩
        obtain ⟨actualSection,hSection,-⟩ :=
          cov.existsUnique_continuousMap_lifts (ContinuousMap.id U) (b.map z) start rfl
        let γ := intervalCurveLoopFrom b z
        let g : C(unitInterval,A.core.TotalSpace) := actualSection.comp γ
        have hg : A.core.proj ∘ g = γ := by
          funext u
          exact congrFun hSection.2 (γ u)
        have hclosed : g 0 = g 1 := by
          change actualSection (γ 0) = actualSection (γ 1)
          congr 1
          simp [γ,intervalCurveLoopFrom,intervalCircleParameterFrom,intervalCircleParameter]
        exact (cut_cover_lift_closes_iff_even_crossings A b hab z hz g hg).mp hclosed
      have adapter : Nonempty (ChartedSpace (EuclideanHalfSpace 2) U) := by
        let P := EuclideanSpace ℝ (Fin 2)
        let h : P ≃ₜ ℝ × ℝ :=
          (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow (X := ℝ))
        let e : OpenPartialHomeomorph P P := h.toOpenPartialHomeomorph.trans
          ((Real.expPartialHomeomorph.prod (OpenPartialHomeomorph.refl ℝ)).trans
            h.symm.toOpenPartialHomeomorph)
        have es : e.source = univ := by simp [e]
        have et : e.target = {x : P | 0 < x 0} := by
          ext x
          simp [e, h, Homeomorph.finTwoArrow, Real.expPartialHomeomorph]
          rfl
        have ep (x : P) : 0 < e x 0 := by
          have hh := e.map_source (show x ∈ e.source by rw [es]; trivial)
          rwa [et] at hh
        let a : OpenPartialHomeomorph P (EuclideanHalfSpace 2) := {
          toFun := fun x => ⟨e x, le_of_lt (ep x)⟩
          invFun := fun y => e.symm y.val
          source := univ
          target := {y | 0 < y.val 0}
          map_source' := fun x _ => ep x
          map_target' := fun _ _ => mem_univ _
          left_inv' := fun x _ => e.left_inv (by rw [es]; trivial)
          right_inv' := by
            intro y hy
            apply Subtype.ext
            exact e.right_inv (by rwa [et])
          open_source := isOpen_univ
          open_target := isOpen_lt continuous_const
            (((continuous_apply 0).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous).comp continuous_subtype_val)
          continuousOn_toFun := by
            apply Continuous.continuousOn
            exact (continuousOn_univ.mp (by simpa only [es] using e.continuousOn)).subtype_mk _
          continuousOn_invFun := by
            apply e.symm.continuousOn.comp continuous_subtype_val.continuousOn
            intro y hy
            rwa [e.symm_source, et]
        }
        letI : ChartedSpace (EuclideanHalfSpace 2) P := {
          atlas := {a}
          chartAt := fun _ => a
          mem_chart_source := fun _ => mem_univ _
          chart_mem_atlas := fun _ => mem_singleton _
        }
        exact ⟨ChartedSpace.comp (EuclideanHalfSpace 2) P U⟩
      letI : ChartedSpace (EuclideanHalfSpace 2) U := adapter.some
      have regularize {S' : Type} [TopologicalSpace S'] [T2Space S']
          [SecondCountableTopology S'] [ChartedSpace (EuclideanHalfSpace 2) S']
          [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S']
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S']
          (K : Set S') (hK : IsCompact K) :
          ∃ (T : PartialTriangulation S') (R : T.toIntrinsic.Subdivision)
            (selected : Finset R.refined.Vertex) (N : Set S'),
            N = T.embed '' {x : T.toIntrinsic.realization |
              (1 : ℝ) / 2 ≤ ∑ v ∈ selected, (R.homeo.symm x).val v} ∧
            IsCompact N ∧ K ⊆ interior N ∧ N ⊆ interior T.support ∧
            (∀ v : R.refined.UsedVertex,
              T.embed (R.homeo (R.refined.vertexPoint v)) ∉ frontier N) ∧
            ∀ edge : R.refined.Edge,
              (edge.val ∩ selected).Nonempty → ¬ edge.val ⊆ selected →
              (R.refined.faces.filter fun face => edge.val ⊆ face).card = 2 := by
        classical
        have hPL :     ∃ (T : PartialTriangulation S') (R : T.toIntrinsic.Subdivision)
            (s : Finset R.refined.Vertex) (N : Set S'),
            N = T.embed '' {x : T.toIntrinsic.realization |
              (1 : ℝ) / 2 ≤ ∑ v ∈ s, (R.homeo.symm x).val v} ∧
            IsCompact N ∧ K ⊆ interior N ∧ N ⊆ interior T.support ∧
            ∀ v : R.refined.UsedVertex,
              T.embed (R.homeo (R.refined.vertexPoint v)) ∉ frontier N := by
            have hpoly :     ∃ T : PartialTriangulation S', IsCompact T.support ∧ K ⊆ interior T.support ∧
                T.BoundaryFacewiseRegular ∧
                ∀ e ∈ T.edges, (T.faces.filter fun t => e ⊆ t).card ≤ 2 := by
                classical
                have hstep
                    (c : MoiseChart S') (hc : c.BoundaryFaithful)
                    {T : PartialTriangulation S'} {A : Set S'} (hT : RadoInvariant T A) :
                    ∃ T' : PartialTriangulation S', RadoInvariant T' (A ∪ c.core) := by
                
                  classical
                  have hweld
                      (c : MoiseChart S') (hc : c.BoundaryFaithful)
                      {T : PartialTriangulation S'} {A : Set S'} (hT : RadoInvariant T A) :
                      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
                        (F₁ F₂ : Finset (Finset V))
                        (e₁ : GeometricRealization V F₁ → S') (e₂ : GeometricRealization V F₂ → S'),
                        (∀ t ∈ F₁ ∪ F₂, t.card = 3) ∧
                        _root_.Topology.IsEmbedding e₁ ∧ _root_.Topology.IsEmbedding e₂ ∧
                        (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
                          (x : V → ℝ) = (y : V → ℝ) → e₁ x = e₂ y) ∧
                        (∀ (x : GeometricRealization V F₁) (y : GeometricRealization V F₂),
                          e₁ x = e₂ y → (x : V → ℝ) = (y : V → ℝ)) ∧
                        PartialTriangulation.BoundaryFacewiseRegularEmbedding F₁ e₁ ∧
                        PartialTriangulation.BoundaryFacewiseRegularEmbedding F₂ e₂ ∧
                        A ∪ c.core ⊆ interior (Set.range e₁ ∪ Set.range e₂) := by
                  
                    classical
                    have hboundaryStraight
                        (T : PartialTriangulation S') (c : MoiseChart S') (hc : c.BoundaryFaithful)
                        (hboundary : T.BoundaryFacewiseRegular) :
                        BoundaryPreservingStraightening S' T c := by
                      have hstraightAway
                          (T : PartialTriangulation S') (c : MoiseChart S')
                          (hc : c.BoundaryFaithful)
                          (hboundary : T.BoundaryFacewiseRegular)
                          (A : Set S') (hA : IsClosed A) :
                          ∃ (U : Set T.toIntrinsic.realization) (_ : IsOpen U)
                            (V : Set Plane) (_ : IsOpen V)
                            (Q : PolygonalReplacementPresentation U V)
                            (_ : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q)
                            (g' : U → c.kind.modelRegion)
                            (g : T.toIntrinsic.realization → S'),
                            V ⊆ c.kind.perturbationRegion ∧
                            (∀ z : c.kind.modelRegion, (z : Plane) ∉ V →
                              (c.chart.symm z).1 ∈ A) ∧
                            (∀ y : T.chartOverlap c, T.embed y.1 ∈ A →
                              T.chartOverlapMap c y ∉ V) ∧
                            (∀ y : T.chartOverlap c, y.1 ∉ U → T.embed y.1 ∈ A) ∧
                            (∀ y : U, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) ∧
                            (∀ (_hk : c.kind = ChartKind.halfDisk) (y : U),
                              (Q.sourceHomeomorph y).1.1 0 = 0 ↔
                                T.embed y.1 ∈
                                  (modelWithCornersEuclideanHalfSpace 2).boundary S') ∧
                            U ⊆ T.chartOverlap c ∧
                            (∀ y : U, g y.1 = (c.chart.symm (g' y)).1) ∧
                            (∀ x, T.embed x ∈ A → g x = T.embed x) ∧
                            MatchesAtFrontier U g T.embed ∧
                            ContinuousOn g U ∧
                            Set.InjOn g U ∧
                            Disjoint (g '' U) (T.embed '' Uᶜ) ∧
                            _root_.Topology.IsEmbedding (frontierGlue U g T.embed) := by
                        classical
                        have hstraightOpen
                            (T : PartialTriangulation S') (c : MoiseChart S')
                            (hc : c.BoundaryFaithful)
                            (hboundary : T.BoundaryFacewiseRegular)
                            (U : Set T.toIntrinsic.realization) (hU : IsOpen U)
                            (hsub : U ⊆ T.chartOverlap c)
                            (V : Set Plane) (hV : IsOpen V)
                            (hVsub : V ⊆ c.kind.perturbationRegion)
                            (hmem : ∀ x : U,
                              T.chartOverlapMap c ⟨x.1, hsub x.2⟩ ∈ V)
                            (hfVclosed : _root_.Topology.IsClosedEmbedding
                              (fun x : U ↦
                                (⟨T.chartOverlapMap c ⟨x.1, hsub x.2⟩, hmem x⟩ : V))) :
                            ∃ (Q : PolygonalReplacementPresentation U V)
                              (_ : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q)
                              (g' : U → c.kind.modelRegion)
                              (g : T.toIntrinsic.realization → S'),
                              (∀ y : U, (g' y : Plane) = (Q.sourceHomeomorph y).1.1) ∧
                              (∀ (_hk : c.kind = ChartKind.halfDisk) (y : U),
                                (Q.sourceHomeomorph y).1.1 0 = 0 ↔
                                  T.embed y.1 ∈
                                    (modelWithCornersEuclideanHalfSpace 2).boundary S') ∧
                              (∀ y : U, g y.1 = (c.chart.symm (g' y)).1) ∧
                              (∀ x, x ∉ U → g x = T.embed x) ∧
                              MatchesAtFrontier U g T.embed ∧
                              ContinuousOn g U ∧
                              Set.InjOn g U ∧
                              Disjoint (g '' U) (T.embed '' Uᶜ) ∧
                              _root_.Topology.IsEmbedding (frontierGlue U g T.embed) := by
                          classical
                          letI : LocallyCompactSpace (EuclideanHalfSpace 2) := by
                            change LocallyCompactSpace {x : EuclideanSpace ℝ (Fin 2) // 0 ≤ x 0}
                            have hc : IsClosed {x : EuclideanSpace ℝ (Fin 2) | 0 ≤ x 0} :=
                              isClosed_le continuous_const (by fun_prop)
                            exact hc.isLocallyClosed.locallyCompactSpace
                          letI : LocallyCompactSpace S' :=
                            ChartedSpace.locallyCompactSpace (EuclideanHalfSpace 2) S'
                          letI : TopologicalSpace.MetrizableSpace S' := inferInstance
                          letI : MetricSpace S' := TopologicalSpace.metrizableSpaceMetric S' 
                          let toOverlap : U → T.chartOverlap c := fun x ↦ ⟨x.1, hsub x.2⟩
                          have htoOverlapEmbedding : _root_.Topology.IsEmbedding toOverlap := by
                            simpa [toOverlap] using _root_.Topology.IsEmbedding.inclusion hsub
                          let f : U → Plane := fun x ↦ T.chartOverlapMap c (toOverlap x)
                          have hf : Continuous f :=
                            (T.isEmbedding_chartOverlapMap c).continuous.comp
                              htoOverlapEmbedding.continuous
                          obtain ⟨mu, hmu, hmatch⟩ :=
                            exists_chartMatchingControlOn_of_metricSpace T c U hU hsub
                          let C₀ := T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
                            (regionSafeControl V f mu)
                            (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)
                          letI : T.toIntrinsic.AdaptiveSafety U := C₀.safety
                          letI : IntrinsicTwoComplex.AdaptiveSafety.IsAdmissible
                              (K := T.toIntrinsic) (U := U) := C₀.safety_isAdmissible
                          let R := T.toIntrinsic.regionControlledAdaptiveComplex U hU V hV f hf hmem mu hmu
                          have hRsupport : R.support = Set.univ := by
                            exact IntrinsicTwoComplex.AdaptiveOpenCover.locallyFiniteTriangleComplex_support
                              T.toIntrinsic U
                              (T.toIntrinsic.controlledAdaptiveOpenCover U hU f hf
                                (regionSafeControl V f mu)
                                (stronglyPositiveOn_regionSafeControl hV hf hmem hmu)) hU
                          let toU : R.support → U := Subtype.val
                          have htoUclosed : _root_.Topology.IsClosedEmbedding toU := by
                            refine ⟨_root_.Topology.IsEmbedding.subtypeVal, ?_⟩
                            rw [show Set.range toU = R.support by exact Subtype.range_val, hRsupport]
                            exact isClosed_univ
                          have hfVrestricted : _root_.Topology.IsClosedEmbedding
                              (fun p : R.support ↦ (⟨f p.1, hmem p.1⟩ : V)) := by
                            have heq : (fun p : R.support ↦ (⟨f p.1, hmem p.1⟩ : V)) =
                                (fun x : U ↦
                                  (⟨T.chartOverlapMap c ⟨x.1, hsub x.2⟩, hmem x⟩ : V)) ∘ toU := by
                              funext p
                              apply Subtype.ext
                              rfl
                            rw [heq]
                            exact hfVclosed.comp htoUclosed
                          let G : R.PlaneGraphRealization :=
                            LocallyFiniteTriangleComplex.PlaneGraphRealization.ofEmbeddingInOpenRegion
                              V hV (fun p ↦ f p.1)
                              ((T.isEmbedding_chartOverlapMap c).comp htoOverlapEmbedding |>.comp
                                _root_.Topology.IsEmbedding.subtypeVal)
                              (fun p ↦ hmem p.1) hfVrestricted.isClosed_range
                          have hGmap : ∀ p, G.map p = f p.1 := fun _ ↦ rfl
                          have hGregion : G.region = V := rfl
                          obtain ⟨vc, hvc, ec, hec, H, hclose⟩ :=
                            IntrinsicTwoComplex.RegionControlledAdaptiveComplex.exists_polygonalReplacement_of_comparison
                              T.toIntrinsic U hU V hV f hf hmem mu hmu G hGmap hGregion
                          let G' := G.withApproximationControls vc hvc ec hec
                          let uToSupport : U → R.support := fun x ↦ ⟨x, by rw [hRsupport]; trivial⟩
                          let eU : U ≃ₜ R.support :=
                            { toFun := uToSupport
                              invFun := Subtype.val
                              left_inv := fun x ↦ rfl
                              right_inv := fun x ↦ Subtype.ext rfl
                              continuous_toFun := Continuous.subtype_mk continuous_id _
                              continuous_invFun := continuous_subtype_val }
                          let q := (diskSourcePrivate straightenedChartOpenSourceHomeomorph) R G' H hRsupport
                          let Q := (diskSourcePrivate straightenedChartOpenPresentation) R G' H hRsupport
                          have hfcoord : ∀ x, f x = T.chartOverlapMap c ⟨x.1, hsub x.2⟩ := fun _ ↦ rfl
                          have hqzero :
                              ∀ (_hk : c.kind = ChartKind.halfDisk) (y : U),
                                (q y).1.1 0 = 0 ↔
                                  T.embed y.1 ∈
                                    (modelWithCornersEuclideanHalfSpace 2).boundary S' := by
                            exact (diskSourcePrivate straightenedChartOpen_coordZero_iff_boundary) T c hc hboundary U hU hsub V hV
                              f hf hmem hfcoord mu hmu G' H hRsupport hGmap
                          let A : PolygonalReplacementSourceAtlas T.toIntrinsic U V Q :=
                            (diskSourcePrivate straightenedChartOpenSourceAtlas) T U hU V hV f hf hmem mu hmu G' H hRsupport
                          have hqmodel : ∀ y : U, (q y).1.1 ∈ c.kind.modelRegion := by
                            intro y
                            cases hk : c.kind with
                            | disk =>
                                have hyPerturb : (q y).1.1 ∈ c.kind.perturbationRegion :=
                                  hVsub (q y).1.2
                                simpa [ChartKind.modelRegion, ChartKind.perturbationRegion, hk] using
                                  hyPerturb
                            | halfDisk =>
                                have hfHalf : Set.range f ⊆ HalfPlaneSet := by
                                  rintro z ⟨x, rfl⟩
                                  have hx := (T.chartOverlapModelMap c (toOverlap x)).2
                                  change f x ∈ c.kind.modelRegion at hx
                                  rw [hk] at hx
                                  simpa [ChartKind.modelRegion, HalfPlaneSet] using hx.2
                                have hgraph : Set.range G'.graphReplacementMap ⊆ HalfPlaneSet := by
                                  apply
                                    IntrinsicTwoComplex.ControlledAdaptiveComplex.range_graphReplacementMap_subset_halfPlane
                                    T.toIntrinsic U hU f hf (regionSafeControl V f mu)
                                      (stronglyPositiveOn_regionSafeControl hV hf hmem hmu) G'
                                  · intro p
                                    rfl
                                  · exact hfHalf
                                have hhalf : (q y).1.1 ∈ HalfPlaneSet := by
                                  exact LocallyFiniteTriangleComplex.polygonalReplacementHomeomorph_mem_halfPlane
                                    G' H hgraph (eU y)
                                exact ⟨by
                                    have hyPerturb : (q y).1.1 ∈ c.kind.perturbationRegion :=
                                      hVsub (q y).1.2
                                    simpa [ChartKind.perturbationRegion, hk] using hyPerturb,
                                  by simpa [HalfPlaneSet] using hhalf⟩
                          let g' : U → c.kind.modelRegion := fun y ↦ ⟨(q y).1.1, hqmodel y⟩
                          let g : T.toIntrinsic.realization → S' := fun x ↦
                            if hx : x ∈ U then (c.chart.symm (g' ⟨x, hx⟩)).1 else T.embed x
                          have hgval : ∀ y : U, g y.1 = (c.chart.symm (g' y)).1 := by
                            intro y
                            simp [g, y.2]
                          have hgoutside : ∀ x, x ∉ U → g x = T.embed x := by
                            intro x hx
                            simp [g, hx]
                          have hgclose : ∀ y : U,
                              dist (g' y : Plane)
                                (T.chartOverlapMap c ⟨y.1, hsub y.2⟩) ≤ mu y := by
                            intro y
                            change dist (q y).1.1 (f y) ≤ mu y
                            have h := hclose (eU y)
                            change dist (q y).1.1 (G.map (eU y)) ≤ mu y at h
                            rw [hGmap] at h
                            exact h
                          obtain ⟨hgmatch, hcross⟩ := hmatch g' g hgval hgclose
                          have hgcont : ContinuousOn g U := by
                            have hg'cont : Continuous g' := by
                              apply Continuous.subtype_mk
                              exact (continuous_subtype_val.comp
                                (continuous_subtype_val.comp q.continuous))
                            have hcomp : Continuous (fun y : U ↦ (c.chart.symm (g' y)).1) :=
                              continuous_subtype_val.comp (c.chart.symm.continuous.comp hg'cont)
                            rw [continuousOn_iff_continuous_restrict]
                            exact hcomp.congr fun y ↦ (hgval y).symm
                          have hginj : Set.InjOn g U := by
                            intro x hx y hy hxy
                            let xU : U := ⟨x, hx⟩
                            let yU : U := ⟨y, hy⟩
                            have hchart : c.chart.symm (g' xU) = c.chart.symm (g' yU) := by
                              apply Subtype.ext
                              rw [← hgval xU, ← hgval yU]
                              exact hxy
                            have hg'eq : g' xU = g' yU := c.chart.symm.injective hchart
                            have hqeq : q xU = q yU := by
                              apply Subtype.ext
                              apply Subtype.ext
                              exact congrArg (fun z : c.kind.modelRegion => (z : Plane)) hg'eq
                            exact congrArg Subtype.val (q.injective hqeq)
                          have hembed : _root_.Topology.IsEmbedding (frontierGlue U g T.embed) :=
                            isEmbedding_frontierGlue_of_matches hU hgcont T.isEmbedding.continuous
                              hgmatch hginj T.isEmbedding.injective hcross
                          exact ⟨Q, A, g', g, fun _ ↦ rfl, hqzero, hgval, hgoutside, hgmatch, hgcont,
                            hginj, hcross, hembed⟩
                        
                        let O : Set T.toIntrinsic.realization := T.chartOverlap c
                        let F : O → c.kind.perturbationRegion :=
                          T.chartOverlapPerturbationMap c
                        let B : Set O := {y | T.embed y.1 ∈ A}
                        have hBclosed : IsClosed B := by
                          exact hA.preimage
                            (T.isEmbedding.continuous.comp continuous_subtype_val)
                        let K : Set c.kind.perturbationRegion := F '' B
                        have hKclosed : IsClosed K := by
                          exact (T.isClosedEmbedding_chartOverlapPerturbationMap c).isClosedMap B hBclosed
                        let V : Set Plane := Subtype.val '' Kᶜ
                        have hV : IsOpen V := by
                          exact c.kind.isOpen_perturbationRegion.isOpenEmbedding_subtypeVal.isOpenMap
                            Kᶜ hKclosed.isOpen_compl
                        have hVsub : V ⊆ c.kind.perturbationRegion := by
                          rintro z ⟨w, -, rfl⟩
                          exact w.2
                        have hVavoid : ∀ z : c.kind.modelRegion, (z : Plane) ∉ V →
                            (c.chart.symm z).1 ∈ A := by
                          intro z hzV
                          let zPert : c.kind.perturbationRegion :=
                            c.kind.modelToPerturbation z
                          have hzK : zPert ∈ K := by
                            by_contra hzK
                            apply hzV
                            exact ⟨zPert, hzK, rfl⟩
                          obtain ⟨y, hyB, hFy⟩ := hzK
                          have hmodel : T.chartOverlapModelMap c y = z := by
                            apply c.kind.isClosedEmbedding_modelToPerturbation.injective
                            exact hFy
                          have hsurface : T.embed y.1 = (c.chart.symm z).1 := by
                            calc
                              T.embed y.1 =
                                  (c.chart.symm (T.chartOverlapModelMap c y)).1 := by
                                symm
                                exact congrArg Subtype.val
                                  (c.chart.symm_apply_apply (T.chartOverlapToDomain c y))
                              _ = (c.chart.symm z).1 :=
                                congrArg (fun w : c.kind.modelRegion ↦ (c.chart.symm w).1) hmodel
                          rw [← hsurface]
                          exact hyB
                        have hVprotected : ∀ y : T.chartOverlap c, T.embed y.1 ∈ A →
                            T.chartOverlapMap c y ∉ V := by
                          intro y hyA hyV
                          obtain ⟨z, hzNotK, hzval⟩ := hyV
                          have hFy : F y = z := by
                            apply Subtype.ext
                            exact hzval.symm
                          apply hzNotK
                          rw [← hFy]
                          exact ⟨y, hyA, rfl⟩
                        let U : Set T.toIntrinsic.realization := Subtype.val '' Bᶜ
                        have hU : IsOpen U := by
                          exact (T.isOpen_chartOverlap c).isOpenEmbedding_subtypeVal.isOpenMap
                            Bᶜ hBclosed.isOpen_compl
                        have hsub : U ⊆ T.chartOverlap c := by
                          rintro x ⟨y, -, rfl⟩
                          exact y.2
                        have hUprotected : ∀ y : T.chartOverlap c, y.1 ∉ U →
                            T.embed y.1 ∈ A := by
                          intro y hyU
                          by_contra hyA
                          apply hyU
                          exact ⟨y, hyA, rfl⟩
                        have hmem : ∀ x : U,
                            T.chartOverlapMap c ⟨x.1, hsub x.2⟩ ∈ V := by
                          intro x
                          rcases x.2 with ⟨y, hyB, hyx⟩
                          have hyval : y.1 = x.1 := hyx
                          have hnotK : F y ∈ Kᶜ := by
                            intro hyK
                            rcases hyK with ⟨b, hbB, hFb⟩
                            have hyb : y = b :=
                              (T.isClosedEmbedding_chartOverlapPerturbationMap c).injective
                                (by simpa [F] using hFb.symm)
                            exact hyB (hyb ▸ hbB)
                          refine ⟨F y, hnotK, ?_⟩
                          change (F y : Plane) =
                            T.chartOverlapMap c ⟨x.1, hsub x.2⟩
                          change T.chartOverlapMap c y =
                            T.chartOverlapMap c ⟨x.1, hsub x.2⟩
                          congr 1
                          exact Subtype.ext hyval
                        let fV : U → V := fun x ↦
                          ⟨T.chartOverlapMap c ⟨x.1, hsub x.2⟩, hmem x⟩
                        have hfVembed : _root_.Topology.IsEmbedding fV := by
                          apply (_root_.Topology.IsEmbedding.subtypeVal.of_comp_iff).mp
                          have hinc : _root_.Topology.IsEmbedding
                              (Set.inclusion hsub : U → T.chartOverlap c) :=
                            _root_.Topology.IsEmbedding.inclusion hsub
                          have hcomp := (T.isEmbedding_chartOverlapMap c).comp hinc
                          simpa [fV, Function.comp_def] using hcomp
                        let j : V → c.kind.perturbationRegion :=
                          fun z ↦ ⟨z.1, hVsub z.2⟩
                        have hjcont : Continuous j :=
                          Continuous.subtype_mk continuous_subtype_val _
                        have hrange : Set.range fV = j ⁻¹' Set.range F := by
                          ext z
                          constructor
                          · rintro ⟨x, rfl⟩
                            refine ⟨⟨x.1, hsub x.2⟩, ?_⟩
                            apply Subtype.ext
                            rfl
                          · rintro ⟨y, hyF⟩
                            have hyPlane : (F y : Plane) = z.1 :=
                              congrArg Subtype.val hyF
                            have hyNotB : y ∈ Bᶜ := by
                              intro hyB
                              have hjK : j z ∈ K := ⟨y, hyB, hyF⟩
                              rcases z.2 with ⟨w, hwNotK, hwz⟩
                              have hwEq : w = j z := by
                                apply Subtype.ext
                                exact hwz
                              exact hwNotK (hwEq ▸ hjK)
                            let x : U := ⟨y.1, ⟨y, hyNotB, rfl⟩⟩
                            refine ⟨x, ?_⟩
                            apply Subtype.ext
                            exact hyPlane
                        have hfVclosed : _root_.Topology.IsClosedEmbedding fV := by
                          refine ⟨hfVembed, ?_⟩
                          rw [hrange]
                          exact (T.isClosedEmbedding_chartOverlapPerturbationMap c).isClosed_range.preimage
                            hjcont
                        obtain ⟨Q, Qatlas, g', g, hgcoord, hqzero, hgval, hgoutside, hgmatch, hgcont,
                            hginj, hcross, hembed⟩ :=
                          hstraightOpen T c hc hboundary U hU hsub V hV hVsub hmem
                            hfVclosed
                        have hgfix : ∀ x, T.embed x ∈ A → g x = T.embed x := by
                          intro x hxA
                          apply hgoutside x
                          rintro ⟨y, hyNotB, hyx⟩
                          have hyval : y.1 = x := hyx
                          apply hyNotB
                          change T.embed y.1 ∈ A
                          rw [hyval]
                          exact hxA
                        exact ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
                          hUprotected, hgcoord, hqzero, hsub, hgval, hgfix, hgmatch, hgcont, hginj,
                          hcross, hembed⟩
                      
                    
                      intro A hA
                      obtain ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
                          hUprotected, hgcoord, hqzero, hUsub, hgval, hgfix, hgmatch, hgcont, hginj,
                          hcross, hembed⟩ :=
                        hstraightAway T c hc hboundary A hA
                      refine ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
                        hUprotected, hgcoord, hUsub, hgval, hgfix, hgmatch, hgcont, hginj, hcross,
                        hembed, ?_⟩
                      intro y
                      by_cases hyU : y ∈ U
                      · let yU : U := ⟨y, hyU⟩
                        rw [frontierGlue_of_mem hyU, hgval yU]
                        by_cases hk : c.kind = ChartKind.disk
                        · constructor
                          · exact fun hy ↦ False.elim
                              ((hc.1 hk (c.chart.symm (g' yU)).1
                                (c.chart.symm (g' yU)).2) hy)
                          · exact fun hy ↦ False.elim
                              ((hc.1 hk (T.embed y) (hUsub hyU)) hy)
                        · have hkHalf : c.kind = ChartKind.halfDisk := by
                            cases hkind : c.kind
                            · exact (hk hkind).elim
                            · rfl
                          have hnew :
                              (c.chart.symm (g' yU)).1 ∈
                                  (modelWithCornersEuclideanHalfSpace 2).boundary S' ↔
                                (g' yU : Plane) 0 = 0 := by
                            have h :=
                              hc.2 hkHalf (c.chart.symm (g' yU)).1
                                (c.chart.symm (g' yU)).2
                            have happly := c.chart.apply_symm_apply (g' yU)
                            have hplane :=
                              congrArg (fun z : c.kind.modelRegion ↦ (z : Plane)) happly
                            rw [hplane] at h
                            exact h
                          calc
                            (c.chart.symm (g' yU)).1 ∈
                                  (modelWithCornersEuclideanHalfSpace 2).boundary S' ↔
                                (g' yU : Plane) 0 = 0 := hnew
                            _ ↔ (Q.sourceHomeomorph yU).1.1 0 = 0 := by
                              rw [hgcoord yU]
                            _ ↔ T.embed y ∈
                                  (modelWithCornersEuclideanHalfSpace 2).boundary S' :=
                              hqzero hkHalf yU
                      · rw [frontierGlue_of_notMem hyU]
                    
                    have hstraight := hboundaryStraight T c hc hT.boundaryFacewiseRegular
                    letI : LocallyCompactSpace (EuclideanHalfSpace 2) := by
                      change LocallyCompactSpace {x : EuclideanSpace ℝ (Fin 2) // 0 ≤ x 0}
                      have hc : IsClosed {x : EuclideanSpace ℝ (Fin 2) | 0 ≤ x 0} :=
                        isClosed_le continuous_const (by fun_prop)
                      exact hc.isLocallyClosed.locallyCompactSpace
                    letI : LocallyCompactSpace S' := ChartedSpace.locallyCompactSpace (EuclideanHalfSpace 2) S'
                    obtain ⟨B, hBopen, hAB, hclosure⟩ :=
                      hT.coresCompact.exists_isOpen_closure_subset
                        (isOpen_interior.mem_nhdsSet.mpr hT.coresInside)
                    let C := closure B
                    have hCclosed : IsClosed C := isClosed_closure
                    have hAC : A ⊆ interior C := by
                      exact hAB.trans (hBopen.subset_interior_iff.mpr subset_closure)
                    obtain ⟨U, hU, V, hV, Q, Qatlas, g', g, hVsub, hVavoid, hVprotected,
                        hUprotected, hgcoord, hUsub, hgval, hgfix, hgmatch, hgcont, hginj, hcross,
                        hembed, hBoundaryPreservation⟩ := hstraight C hCclosed
                    let W : (diskWeldPrivate CrossingWeldStraighteningContext) S' c T A :=
                      (diskWeldPrivate CrossingWeldStraighteningContext.mk) C hCclosed hAC hclosure U hU V hV Q Qatlas g' g
                        hVsub hVavoid hVprotected hUprotected hgcoord hUsub hgval hgfix
                        hgmatch hgcont hginj hcross hembed hBoundaryPreservation
                    obtain ⟨P⟩ := (diskWeldPrivate exists_crossingWeldPatchContext) S' c hc W
                    let geometry : (diskWeldPrivate ChartInductionGeometry) S' c T A P :=
                      (diskWeldPrivate ChartInductionGeometry.canonical) P hT
                    have hboundaryFanSurface :
                        ((diskWeldPrivate ChartInductionGeometry.marking) geometry).markedFanLocallyFiniteTriangleComplex.compactIntrinsic
                          |>.HasSurfaceEdgeValence :=
                      ((diskWeldPrivate ChartInductionGeometry.marking) geometry).markedFanCompactIntrinsic_hasSurfaceEdgeValence
                        ((diskWeldPrivate ChartInductionGeometry.subdivision_surface) geometry)
                    obtain ⟨mixedCertificate⟩ := (diskWeldPrivate exists_canonicalMixedLocalFanCertificate) P hT
                    have selectedFace_of_fanInterval_endpoints_local :=
                      (diskWeldPrivate ChartInductionGeometry.canonicalSelectedFace_of_fanInterval_endpoints_local) P hT
                    let finishContextRaw : (diskWeldPrivate ChartInductionFinishContext) S' c T A P :=
                      (diskWeldPrivate ChartInductionFinishContext.mk) geometry hc hT.boundaryFacewiseRegular
                        mixedCertificate hboundaryFanSurface selectedFace_of_fanInterval_endpoints_local
                    obtain ⟨finishContext, -⟩ := (diskWeldPrivate exists_sealed_copy) finishContextRaw
                    exact (diskWeldPrivate finish_crossing_weld) (S := S') P finishContext
                  
                  by_cases hcore : c.core ⊆ interior T.support
                  · exact ⟨T, hT.absorb_of_subset c.isCompact_core hcore⟩
                  by_cases hA : A ⊆ interior c.patchPartialTriangulation.support
                  · exact ⟨c.patchPartialTriangulation,
                      radoInvariant_chartPatch_absorb c hc hT.coresCompact hA⟩
                  · -- the crossing case: weld the adjusted old complex and the chart patch, then glue
                    obtain ⟨V, _, _, F₁, F₂, e₁, e₂, hcard, he₁, he₂, hagree, hsep,
                        hboundary₁, hboundary₂, hcover⟩ :=
                      hweld c hc hT
                    obtain ⟨T', _vertexEquiv, _hfaces, hsupport, hsurf', hboundary'⟩ :=
                      PartialTriangulation.exists_glued V F₁ F₂ hcard e₁ e₂ he₁ he₂
                        hagree hsep hboundary₁ hboundary₂
                    refine ⟨T', ?_, hsurf', hboundary', ?_⟩
                    · exact (hT.coresCompact.union c.isCompact_core)
                    · rw [hsupport]
                      exact hcover
                
                have localChart (x : S') : ∃ c : MoiseChart S', c.BoundaryFaithful ∧
                    x ∈ interior c.core := by
                  obtain ⟨c, hc, hx⟩ := exists_moiseChart_core_mem_nhds S' x
                  exact ⟨c, hc, mem_interior_iff_mem_nhds.mpr hx⟩
                choose c hc hx using localChart
                obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => interior (c x).core)
                  (fun _ => isOpen_interior) (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
                have finiteAbsorption (t : Finset S') : ∃ T : PartialTriangulation S',
                    RadoInvariant T (⋃ x ∈ t, (c x).core) := by
                  induction t using Finset.induction_on with
                  | empty =>
                    exact ⟨PartialTriangulation.empty S', by simpa using radoInvariant_empty S'⟩
                  | @insert x t hxt ih =>
                    obtain ⟨T, hT⟩ := ih
                    obtain ⟨T', hT'⟩ := hstep (c x) (hc x) hT
                    refine ⟨T', ?_⟩
                    have heq : (⋃ y ∈ insert x t, (c y).core) =
                        (⋃ y ∈ t, (c y).core) ∪ (c x).core := by
                      ext z
                      simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
                      aesop
                    rw [heq]
                    exact hT'
                obtain ⟨T, hT⟩ := finiteAbsorption t
                refine ⟨T, T.isCompact_support, ?_, hT.boundaryFacewiseRegular, hT.combSurface⟩
                intro x hxK
                obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hxK)
                exact hT.coresInside (Set.mem_iUnion₂.mpr ⟨y, hyt, interior_subset hxy⟩)
          
            obtain ⟨T, hTs, hKT, hboundary, hvalence⟩ := hpoly
            have hregular (P : IntrinsicTwoComplex) {C U : Set P.realization}
              (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
              ∃ (R : P.Subdivision) (s : Finset R.refined.Vertex) (N : Set P.realization),
                N = {x | (1 : ℝ) / 2 ≤ ∑ v ∈ s, (R.homeo.symm x).val v} ∧
                IsCompact N ∧ C ⊆ interior N ∧ N ⊆ U ∧
                ∀ v : R.refined.UsedVertex,
                  R.homeo (R.refined.vertexPoint v) ∉ frontier N := by
                have hcut :     ∃ (R : P.Subdivision) (s : Finset R.refined.Vertex),
                    let f : R.refined.realization → ℝ := fun x => ∑ v ∈ s, x.val v
                    Continuous f ∧
                    (∀ x, R.homeo x ∈ C → f x = 1) ∧
                    (∀ x, 0 < f x → R.homeo x ∈ U) ∧
                    (∀ v : R.refined.UsedVertex, f (R.refined.vertexPoint v) ≠ 1 / 2) := by
                    classical
                    obtain ⟨V, hV, hCV, hVU⟩ :=
                      hC.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hCU)
                    let W : Bool × Bool → Set P.realization := fun i =>
                      (if i.1 then (closure V)ᶜ else U) ∩ (if i.2 then Cᶜ else V)
                    have hW : ∀ i, IsOpen (W i) := by
                      rintro ⟨a,b⟩
                      cases a <;> cases b <;> simp only [W] <;>
                        exact IsOpen.inter (by first | exact hU | exact isClosed_closure.isOpen_compl)
                          (by first | exact hV | exact hC.isClosed.isOpen_compl)
                    have hcover : (univ : Set P.realization) ⊆ ⋃ i, W i := by
                      intro x _
                      have hfirst : ∃ a : Bool, x ∈ if a then (closure V)ᶜ else U := by
                        by_cases hx : x ∈ closure V
                        · exact ⟨false, hVU hx⟩
                        · exact ⟨true, hx⟩
                      have hsecond : ∃ b : Bool, x ∈ if b then Cᶜ else V := by
                        by_cases hx : x ∈ C
                        · exact ⟨false, hCV hx⟩
                        · exact ⟨true, hx⟩
                      obtain ⟨a, ha⟩ := hfirst
                      obtain ⟨b, hb⟩ := hsecond
                      exact mem_iUnion.mpr ⟨(a,b), ha, hb⟩
                    obtain ⟨R, hR⟩ := P.exists_subdivision_subordinate_openCover W hW hcover
                    let s : Finset R.refined.Vertex := Finset.univ.filter fun v =>
                      ∃ w : R.refined.UsedVertex, w.val = v ∧ R.homeo (R.refined.vertexPoint w) ∈ closure V
                    let f : R.refined.realization → ℝ := fun x => ∑ v ∈ s, x.val v
                    have hselected (t : R.refined.Face) (v : t.val) :
                        v.val ∈ s ↔ R.homeo (R.refined.facePoint t v) ∈ closure V := by
                      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
                      constructor
                      · rintro ⟨w, hw, hh⟩
                        have he : w = ⟨v.val, t.val, t.property, v.property⟩ := Subtype.ext hw
                        simpa only [he, IntrinsicTwoComplex.facePoint] using hh
                      · intro hv
                        exact ⟨⟨v.val, t.val, t.property, v.property⟩, rfl, hv⟩
                    refine ⟨R, s, ?_, ?_, ?_, ?_⟩
                    · exact continuous_finsetSum _ fun v _ => (continuous_apply v).comp continuous_subtype_val
                    · intro x hx
                      obtain ⟨t, ht, hxt⟩ := x.property.2
                      let T : R.refined.Face := ⟨t, ht⟩
                      obtain ⟨⟨a,b⟩, hab⟩ := hR t ht
                      have hb : b = false := by
                        cases b
                        · rfl
                        · have hh := (hab x hxt).2
                          exact False.elim (hh hx)
                      have hs : ∀ v ∈ t, v ∈ s := by
                        intro v hv
                        apply (hselected T ⟨v,hv⟩).mpr
                        apply subset_closure
                        have hh := (hab (R.refined.facePoint T ⟨v,hv⟩)
                          (R.refined.facePoint_mem_faceCarrier T ⟨v,hv⟩)).2
                        simpa [W, hb] using hh
                      change (∑ v ∈ s, x.val v) = 1
                      rw [← x.property.1.2]
                      apply Finset.sum_subset (Finset.subset_univ s)
                      intro v _ hvs
                      exact hxt v (fun hvt => hvs (hs v hvt))
                    · intro x hx
                      obtain ⟨t, ht, hxt⟩ := x.property.2
                      let T : R.refined.Face := ⟨t, ht⟩
                      have hp : ∃ v ∈ s, 0 < x.val v := by
                        by_contra hn
                        push_neg at hn
                        have hnSum : f x ≤ 0 := Finset.sum_nonpos hn
                        exact (not_lt_of_ge hnSum) hx
                      obtain ⟨v, hv, hvpos⟩ := hp
                      have hvt : v ∈ t := by
                        by_contra hn
                        have hz := hxt v hn
                        linarith
                      have hvertex := (hselected T ⟨v,hvt⟩).mp hv
                      obtain ⟨⟨a,b⟩, hab⟩ := hR t ht
                      have ha : a = false := by
                        cases a
                        · rfl
                        · have hh := (hab (R.refined.facePoint T ⟨v,hvt⟩)
                            (R.refined.facePoint_mem_faceCarrier T ⟨v,hvt⟩)).1
                          exact False.elim (hh hvertex)
                      have hh := (hab x hxt).1
                      simpa [W, ha] using hh
                    · intro v
                      change (∑ w ∈ s, (Pi.single v.val (1 : ℝ)) w) ≠ 1 / 2
                      simp only [Pi.single_apply]
                      by_cases hv : v.val ∈ s <;> simp [hv]
              
                obtain ⟨R, s, hf, hCeq, hUpos, hvertices⟩ := hcut
                let f : R.refined.realization → ℝ := fun x => ∑ v ∈ s, x.val v
                let F : P.realization → ℝ := f ∘ R.homeo.symm
                have hF : Continuous F := hf.comp R.homeo.symm.continuous
                let N : Set P.realization := {x | (1 : ℝ) / 2 ≤ F x}
                have hNclosed : IsClosed N := isClosed_le continuous_const hF
                refine ⟨R, s, N, rfl, hNclosed.isCompact, ?_, ?_, ?_⟩
                · have hO : IsOpen {x | (1 : ℝ) / 2 < F x} := isOpen_lt continuous_const hF
                  have hON : {x | (1 : ℝ) / 2 < F x} ⊆ N := fun x hx => show (1 : ℝ) / 2 ≤ F x from le_of_lt hx
                  apply Subset.trans _ (hO.subset_interior_iff.mpr hON)
                  intro x hx
                  have he : F x = 1 := by
                    exact hCeq (R.homeo.symm x) (by simpa using hx)
                  change (1 : ℝ) / 2 < F x
                  rw [he]
                  norm_num
                · intro x hx
                  have hp : 0 < f (R.homeo.symm x) := by
                    change (1 : ℝ) / 2 ≤ f (R.homeo.symm x) at hx
                    linarith
                  simpa using hUpos (R.homeo.symm x) hp
                · intro v hv
                  have he := frontier_le_subset_eq continuous_const hF hv
                  change (1 : ℝ) / 2 = F (R.homeo (R.refined.vertexPoint v)) at he
                  have he' : f (R.refined.vertexPoint v) = 1 / 2 := by
                    simpa only [F, Function.comp_apply, R.homeo.symm_apply_apply, eq_comm] using he
                  exact hvertices v he'
          
            let C : Set T.toIntrinsic.realization := T.embed ⁻¹' K
            let U : Set T.toIntrinsic.realization := T.embed ⁻¹' interior T.support
            have hC : IsCompact C := (hK.isClosed.preimage T.isEmbedding.continuous).isCompact
            have hU : IsOpen U := isOpen_interior.preimage T.isEmbedding.continuous
            obtain ⟨R, s, A, hAeq, hA, hCA, hAU, hav⟩ := hregular T.toIntrinsic hC hU (fun x hx => hKT hx)
            have hImageInterior : T.embed '' interior A ⊆ interior (T.embed '' A) := by
              obtain ⟨O, hO, hEq⟩ := T.isEmbedding.isInducing.image_eq_isOpen_inter_range isOpen_interior
              have hsub : O ∩ interior T.support ⊆ T.embed '' A := by
                intro y hy
                have hyr : y ∈ Set.range T.embed := interior_subset hy.2
                have hyA : y ∈ T.embed '' interior A := by rw [hEq]; exact ⟨hy.1, hyr⟩
                exact Set.image_mono interior_subset hyA
              have hOpen : IsOpen (O ∩ interior T.support) := hO.inter isOpen_interior
              intro y hy
              apply (hOpen.subset_interior_iff.mpr hsub)
              have hyO : y ∈ O := by rw [hEq] at hy; exact hy.1
              obtain ⟨x, hx, hxy⟩ := hy
              exact ⟨hyO, hxy ▸ hAU (interior_subset hx)⟩
            refine ⟨T, R, s, T.embed '' A, ?_, hA.image T.isEmbedding.continuous, ?_, ?_, ?_⟩
            · rw [hAeq]
            · intro y hy
              have hyr : y ∈ T.support := interior_subset (hKT hy)
              obtain ⟨x, hxy⟩ := hyr
              apply hImageInterior
              exact ⟨x, hCA (by change T.embed x ∈ K; rwa [hxy]), hxy⟩
            · rintro y ⟨x,hx,hxy⟩
              exact hxy ▸ hAU hx
            · intro v hv
              let x := R.homeo (R.refined.vertexPoint v)
              have hclosed : IsClosed (T.embed '' A) := (hA.image T.isEmbedding.continuous).isClosed
              have hxA : x ∈ A := by
                have hi : T.embed x ∈ T.embed '' A := by
                  exact hclosed.closure_eq ▸ frontier_subset_closure hv
                obtain ⟨w, hw, he⟩ := hi
                exact T.isEmbedding.injective he ▸ hw
              have hxi : x ∈ interior A := by
                by_contra hn
                apply hav v
                exact ⟨subset_closure hxA, hn⟩
              exact hv.2 (hImageInterior ⟨x, hxi, rfl⟩)
        have htwoFaces (P : IntrinsicTwoComplex) (ι : P.realization → S')
          (hι : _root_.Topology.IsEmbedding ι)
          (e : Finset P.Vertex) (he : e.card = 2) (x : P.realization)
          (hxpos : ∀ v ∈ e, 0 < x.val v) (hxzero : ∀ v ∉ e, x.val v = 0)
          (hxint : ι x ∈ interior (range ι)) :
          2 ≤ (P.faces.filter fun t => e ⊆ t).card := by
            classical
            have hreflect  {X : Type} [TopologicalSpace X]
              {f : X → S'} {g : X → EuclideanSpace ℝ (Fin 2)}
              (hf : _root_.Topology.IsEmbedding f) (hg : _root_.Topology.IsEmbedding g)
              {x : X} (hx : f x ∈ interior (range f)) :
              g x ∈ interior (range g) := by
                let P := EuclideanSpace ℝ (Fin 2)
                let z : S' := f x
                let c : OpenPartialHomeomorph S' P := chartAt P z
                let W : Set P :=
                  c.target ∩ c.symm ⁻¹' interior (Set.range f)
                have hWopen : IsOpen W := by
                  exact c.continuousOn_symm.isOpen_inter_preimage c.open_target isOpen_interior
                have hzTarget : c z ∈ c.target := c.map_source (ChartedSpace.mem_chart_source z)
                have hcz : c.symm (c z) = z :=
                  c.left_inv (ChartedSpace.mem_chart_source z)
                have hczW : c z ∈ W := by
                  refine ⟨hzTarget, ?_⟩
                  change c.symm (c z) ∈ interior (Set.range f)
                  rw [hcz]
                  exact hx
                have hcSymm : Continuous (fun w : W ↦ c.symm w.1) := by
                  apply ContinuousOn.restrict
                  exact c.continuousOn_symm.mono fun w hw ↦ hw.1
                let toOldRange : W → Set.range f :=
                  fun w ↦ ⟨c.symm w.1, interior_subset w.2.2⟩
                have htoOldRange : Continuous toOldRange :=
                  Continuous.subtype_mk hcSymm _
                let source : W → X :=
                  fun w ↦ hf.toHomeomorph.symm (toOldRange w)
                have hsourceCont : Continuous source :=
                  hf.toHomeomorph.symm.continuous.comp htoOldRange
                have hsourceInj : Function.Injective source := by
                  intro u v huv
                  have huvRange : toOldRange u = toOldRange v :=
                    hf.toHomeomorph.symm.injective huv
                  have huvSurface : c.symm u.1 = c.symm v.1 :=
                    congrArg Subtype.val huvRange
                  apply Subtype.ext
                  exact c.symm.injOn u.2.1 v.2.1
                    huvSurface
                let localMap : W → P := fun w ↦ g (source w)
                have hlocalCont : Continuous localMap :=
                  hg.continuous.comp hsourceCont
                have hlocalInj : Function.Injective localMap :=
                  hg.injective.comp hsourceInj
                have hlocalOpen : IsOpen (Set.range localMap) :=
                  isOpen_range_of_isOpen_of_continuous_injective
                    (modelWithCornersSelf ℝ P) hWopen localMap
                    hlocalCont hlocalInj
                let w₀ : W := ⟨c z, hczW⟩
                have hsourceW₀ : source w₀ = x := by
                  apply hf.injective
                  change (hf.toHomeomorph (source w₀)).1 = f x
                  rw [hf.toHomeomorph.apply_symm_apply]
                  change c.symm (c z) = f x
                  exact hcz
                have hlocalAt : localMap w₀ = g x := by
                  rw [show localMap w₀ = g (source w₀) by rfl, hsourceW₀]
                apply mem_interior_iff_mem_nhds.mpr
                apply Filter.mem_of_superset
                  (hlocalOpen.mem_nhds ⟨w₀, hlocalAt⟩)
                rintro y ⟨w, rfl⟩
                exact Set.mem_range_self (source w)
          
            by_contra hn
            have hcount : (P.faces.filter fun t => e ⊆ t).card ≤ 1 := by omega
            obtain ⟨t, ht, hxt⟩ := x.property.2
            have het : e ⊆ t := by
              intro v hv
              by_contra hvt
              have hz := hxt v hvt
              have hp := hxpos v hv
              linarith
            have hsole : ∀ u ∈ P.faces, e ⊆ u → u = t := by
              intro u hu heu
              exact (Finset.card_le_one.mp hcount) u (Finset.mem_filter.mpr ⟨hu,heu⟩)
                t (Finset.mem_filter.mpr ⟨ht,het⟩)
            let T : P.Face := ⟨t,ht⟩
            let other : Set S' := ⋃ u : P.Face,
              if u.val = t then ∅ else ι '' P.faceCarrier u.val
            have ho : IsClosed other := by
              apply isClosed_iUnion_of_finite
              intro u
              split_ifs
              · exact isClosed_empty
              · exact ((P.faceCarrier_closed u.val).isCompact.image hι.continuous).isClosed
            have hxo : ι x ∉ other := by
              intro hx
              obtain ⟨u,hu⟩ := mem_iUnion.mp hx
              by_cases hut : u.val = t
              · simpa [hut] using hu
              · simp only [if_neg hut] at hu
                obtain ⟨y,hy,heq⟩ := hu
                have hyx : y = x := hι.injective heq
                subst y
                have heu : e ⊆ u.val := by
                  intro v hv
                  by_contra hvu
                  have hz := hy v hvu
                  have hp := hxpos v hv
                  linarith
                exact hut (hsole u.val u.property heu)
            let W := interior (range ι) ∩ otherᶜ
            have hW : IsOpen W := isOpen_interior.inter ho.isOpen_compl
            let f : P.ClosedFace T → S' := fun y => ι y.val
            have hf : _root_.Topology.IsEmbedding f := hι.comp _root_.Topology.IsEmbedding.subtypeVal
            have hWF : W ⊆ range f := by
              intro z hz
              obtain ⟨y,hy⟩ := interior_subset hz.1
              obtain ⟨u,hu,hyu⟩ := y.property.2
              have hut : u = t := by
                by_contra hut
                apply hz.2
                apply mem_iUnion.mpr
                refine ⟨⟨u,hu⟩, ?_⟩
                simp only [if_neg hut]
                exact ⟨y,hyu,hy⟩
              subst u
              exact ⟨⟨y,hyu⟩,hy⟩
            have hxf : f ⟨x,hxt⟩ ∈ interior (range f) :=
              (hW.subset_interior_iff.mpr hWF) ⟨hxint,hxo⟩
            let g : P.ClosedFace T → Plane := fun y => (P.facePlaneHomeomorph T y).val
            have hg : _root_.Topology.IsEmbedding g :=
              _root_.Topology.IsEmbedding.subtypeVal.comp (P.facePlaneHomeomorph T).isEmbedding
            have hgRange : range g = standardTrianglePlaneComplex.support := by
              ext z
              constructor
              · rintro ⟨y,rfl⟩
                exact (P.facePlaneHomeomorph T y).property
              · intro hz
                refine ⟨(P.facePlaneHomeomorph T).symm ⟨z,hz⟩, ?_⟩
                exact congrArg Subtype.val ((P.facePlaneHomeomorph T).apply_symm_apply ⟨z,hz⟩)
            have hpint := hreflect hf hg hxf
            rw [hgRange] at hpint
            have hnot : ¬ t ⊆ e := by
              intro hte
              have hle := Finset.card_le_card hte
              rw [P.faces_card t ht, he] at hle
              omega
            obtain ⟨v,hvt,hve⟩ := Finset.not_subset.mp hnot
            let p : standardTrianglePlaneComplex.support := P.facePlaneHomeomorph T ⟨x,hxt⟩
            let i : Fin 3 := (P.faceVertexEquiv T).symm ⟨v,hvt⟩
            have hpi : p.val ∈ interior
                (standardTrianglePlaneComplex.toTriangleMesh.triangleCarrier standardTriangleMeshFace.val) := by
              rw [show standardTrianglePlaneComplex.toTriangleMesh.triangleCarrier
                standardTriangleMeshFace.val = standardTrianglePlaneComplex.support by
                  exact standardTriangle_cellCarrier_univ]
              exact hpint
            have hcoord : 0 < standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace p.val i := by
              rw [standardTrianglePlaneComplex.faceCoords_apply_of_mem standardTriangleMeshFace (Finset.mem_univ i)]
              rw [standardTrianglePlaneComplex.toTriangleMesh.interior_triangleCarrier standardTriangleMeshFace] at hpi
              exact hpi (standardTrianglePlaneComplex.toTriangleMesh.triangleEquiv
                standardTriangleMeshFace ⟨i,Finset.mem_univ i⟩)
            have hcoordEq : x.val v = standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace p.val i := by
              calc
                x.val v = ((P.facePlaneHomeomorph T).symm p).val.val v := by
                  have h := (P.facePlaneHomeomorph T).symm_apply_apply ⟨x,hxt⟩
                  exact congrFun (congrArg (fun z => z.val.val) h.symm) v
                _ = P.facePlaneInverseAffine T p.val v :=
                  congrFun (P.facePlaneHomeomorph_symm_val T p) v
                _ = _ := by
                  simp only [IntrinsicTwoComplex.facePlaneInverseAffine, AffineMap.comp_apply,
                    P.faceCoordExtensionAffine_apply_of_mem T
                      (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace p.val) hvt]
                  rfl
            have hz := hxzero v hve
            linarith
      
        obtain ⟨T,R,s,N,hNeq,hN,hKN,hNT,hvertices⟩ := hPL
        refine ⟨T,R,s,N,hNeq,hN,hKN,hNT,hvertices,?_⟩
        intro e hyes hno
        let P := R.refined
        let ι : P.realization → S' := T.embed ∘ R.homeo
        have hι : _root_.Topology.IsEmbedding ι := T.isEmbedding.comp R.homeo.isEmbedding
        let r : Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
        let x : P.realization := P.edgePath e r
        have hxzero : ∀ v ∉ e.val, x.val v = 0 := by
          have hx : x ∈ P.faceCarrier e.val := by
            rw [← P.range_edgePath e]
            exact ⟨r,rfl⟩
          exact hx
        have hxf : x.val (P.edgeFirst e) = 1 / 2 := by
          change (P.edgePath e r).val (P.edgeFirst e) = 1 / 2
          rw [P.edgePath_apply_first]
          norm_num [r]
        have hxs : x.val (P.edgeSecond e) = 1 / 2 := by
          change (P.edgePath e r).val (P.edgeSecond e) = 1 / 2
          rw [P.edgePath_apply_second]
        have hxpos : ∀ v ∈ e.val, 0 < x.val v := by
          intro v hv
          rw [P.edge_eq_pair e] at hv
          rcases Finset.mem_insert.mp hv with hv | hv
          · subst v
            rw [hxf]
            norm_num
          · have hv' := Finset.mem_singleton.mp hv
            subst v
            rw [hxs]
            norm_num
        have habits : (P.edgeFirst e ∈ s ∧ P.edgeSecond e ∉ s) ∨
            (P.edgeSecond e ∈ s ∧ P.edgeFirst e ∉ s) := by
          rw [P.edge_eq_pair e] at hyes hno
          simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hno
          by_cases ha : P.edgeFirst e ∈ s
          · exact Or.inl ⟨ha,fun hb => hno ⟨ha,hb⟩⟩
          · refine Or.inr ⟨?_,ha⟩
            obtain ⟨v,hv⟩ := hyes
            have hvpair := (Finset.mem_inter.mp hv).1
            have hvs := (Finset.mem_inter.mp hv).2
            simp only [Finset.mem_insert,Finset.mem_singleton] at hvpair
            rcases hvpair with rfl | rfl
            · exact False.elim (ha hvs)
            · exact hvs
        have hsum : (∑ v ∈ s, x.val v) = 1 / 2 := by
          rcases habits with ⟨ha,hb⟩ | ⟨hb,ha⟩
          · rw [Finset.sum_eq_single (P.edgeFirst e)]
            · exact hxf
            · intro v hv hne
              apply hxzero
              rw [P.edge_eq_pair e]
              simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
              exact ⟨hne,fun heq => hb (heq ▸ hv)⟩
            · exact fun hn => False.elim (hn ha)
          · rw [Finset.sum_eq_single (P.edgeSecond e)]
            · exact hxs
            · intro v hv hne
              apply hxzero
              rw [P.edge_eq_pair e]
              simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
              exact ⟨fun heq => ha (heq ▸ hv),hne⟩
            · exact fun hn => False.elim (hn hb)
        have hxN : ι x ∈ N := by
          rw [hNeq]
          refine ⟨R.homeo x,?_,rfl⟩
          change (1 : ℝ) / 2 ≤ ∑ v ∈ s, (R.homeo.symm (R.homeo x)).val v
          simp only [R.homeo.symm_apply_apply]
          rw [hsum]
        have hRange : range ι = T.support := by
          ext y
          constructor
          · rintro ⟨w,rfl⟩
            exact ⟨R.homeo w,rfl⟩
          · rintro ⟨w,rfl⟩
            exact ⟨R.homeo.symm w, by simp [ι]⟩
        have hxint : ι x ∈ interior (range ι) := by
          rw [hRange]
          exact hNT hxN
        have hlow := htwoFaces P ι hι e.val (P.card_of_mem_edges e.property) x hxpos hxzero hxint
        have hhigh := edge_valence_le_two_of_isEmbedding P.faces P.faces_card ι hι e.val
          (P.card_of_mem_edges e.property)
        exact Nat.le_antisymm hhigh hlow
      have actualCompactConnectedHull {U : Type} [TopologicalSpace U]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U] [PathConnectedSpace U]
          (K : Set U) (hK : IsCompact K) :
          ∃ L : Set U, IsCompact L ∧ IsConnected L ∧ K ⊆ L := by
        classical
        let base : U := Classical.choice inferInstance
        have hLocal (x : K) : ∃ C : Set U, IsCompact C ∧ IsConnected C ∧ x.val ∈ interior C := by
          obtain ⟨r,hr,ht,hsub,hcomp,hconn,hop,hin⟩ :=
            CurveComplex.exists_compact_chart_disk_in_open x.val Set.univ isOpen_univ (Set.mem_univ _)
          let e := chartAt (EuclideanSpace ℝ (Fin 2)) x.val
          refine ⟨e.symm '' Metric.closedBall (e x.val) r,hcomp,hconn,?_⟩
          exact (interior_mono (Set.image_mono Metric.ball_subset_closedBall))
            (by rwa [IsOpen.interior_eq hop])
        choose C hCc hCconn hxC using hLocal
        obtain ⟨centers,hCover⟩ := hK.elim_finite_subcover (fun x => interior (C x))
          (fun _ => isOpen_interior)
          (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxC ⟨x,hx⟩⟩)
        let connecting (x : K) : Path base x.val := (PathConnectedSpace.joined base x.val).somePath
        let piece (x : K) : Set U := C x ∪ Set.range (connecting x)
        have hPieceCompact (x : K) : IsCompact (piece x) :=
          (hCc x).union (isCompact_range (connecting x).continuous)
        have hPieceConnected (x : K) : IsConnected (piece x) := by
          apply (hCconn x).union
          · exact ⟨x.val,interior_subset (hxC x),⟨1,Path.target _⟩⟩
          · exact isConnected_range (connecting x).continuous
        have hBase (x : K) : base ∈ piece x := Or.inr ⟨0,Path.source _⟩
        have hConnected (f : Finset K) : IsConnected ({base} ∪ ⋃ x ∈ f,piece x) := by
          induction f using Finset.induction_on with
          | empty => simpa using (isConnected_singleton (x := base))
          | @insert x f hx ih =>
            have heq : ({base} ∪ ⋃ z ∈ insert x f,piece z) = ({base} ∪ ⋃ z ∈ f,piece z) ∪ piece x := by
              ext z
              simp only [Finset.mem_insert,Set.mem_union,Set.mem_iUnion]
              aesop
            rw [heq]
            exact ih.union ⟨base,Or.inl (Set.mem_singleton _),hBase x⟩ (hPieceConnected x)
        refine ⟨{base} ∪ ⋃ x ∈ centers,piece x,
          isCompact_singleton.union (centers.isCompact_biUnion (fun x _ => hPieceCompact x)),hConnected centers,?_⟩
        intro x hx
        obtain ⟨z,hz,hin⟩ := mem_iUnion₂.mp (hCover hx)
        exact Or.inr (mem_iUnion₂.mpr ⟨z,hz,Or.inl (interior_subset hin)⟩)
      obtain ⟨originalHull,hHullCompact,hHullConnected,hKHull⟩ := actualCompactConnectedHull K hK
      obtain ⟨T,R,selected,N,hCut,hNCompact,hHullInterior,hNSupport,hNoVertex,hValenceTwo⟩ :=
        regularize originalHull hHullCompact
      have hOriginalK : K ⊆ interior N := hKHull.trans hHullInterior
      let P := R.refined
      let realizationMap : P.realization → U := T.embed ∘ R.homeo
      have hRealizationEmbedding : Topology.IsEmbedding realizationMap :=
        T.isEmbedding.comp R.homeo.isEmbedding
      let cutoff : T.toIntrinsic.realization → ℝ :=
        fun x => ∑ v ∈ selected, (R.homeo.symm x).val v
      have hCutoffContinuous : Continuous cutoff := by
        dsimp [cutoff]
        fun_prop
      let A : Set T.toIntrinsic.realization := {x | (1 : ℝ) / 2 ≤ cutoff x}
      have hAImage : N = T.embed '' A := hCut
      have hImageInterior : T.embed '' interior A ⊆ interior N := by
        obtain ⟨O,hO,hEq⟩ :=
          T.isEmbedding.isInducing.image_eq_isOpen_inter_range isOpen_interior
        have hSub : O ∩ interior T.support ⊆ N := by
          intro y hy
          have hyr : y ∈ Set.range T.embed := interior_subset hy.2
          have hyA : y ∈ T.embed '' interior A := by
            rw [hEq]
            exact ⟨hy.1,hyr⟩
          rw [hAImage]
          exact Set.image_mono interior_subset hyA
        have hOpen : IsOpen (O ∩ interior T.support) := hO.inter isOpen_interior
        intro y hy
        apply hOpen.subset_interior_iff.mpr hSub
        have hyO : y ∈ O := by rw [hEq] at hy; exact hy.1
        have hyN : y ∈ N := by
          rw [hAImage]
          exact Set.image_mono interior_subset hy
        exact ⟨hyO,hNSupport hyN⟩
      have hFrontierLevel (x : P.realization)
          (hx : realizationMap x ∈ frontier N) :
          (∑ v ∈ selected, x.val v) = (1 : ℝ) / 2 := by
        have hxN : realizationMap x ∈ N :=
          hNCompact.isClosed.closure_eq ▸ frontier_subset_closure hx
        have hxA : R.homeo x ∈ A := by
          rw [hAImage] at hxN
          obtain ⟨w,hw,he⟩ := hxN
          have hew : w = R.homeo x := T.isEmbedding.injective he
          exact hew ▸ hw
        have hxNotInterior : R.homeo x ∉ interior A := by
          intro hi
          exact hx.2 (hImageInterior ⟨R.homeo x,hi,rfl⟩)
        have he := frontier_le_subset_eq continuous_const hCutoffContinuous
          (show R.homeo x ∈ frontier A from ⟨subset_closure hxA,hxNotInterior⟩)
        simpa only [Set.mem_setOf_eq,cutoff,R.homeo.symm_apply_apply,eq_comm] using he
      have hFrontierSupport (x : P.realization)
          (hx : realizationMap x ∈ frontier N) :
          let active := Finset.univ.filter fun v : P.Vertex => 0 < x.val v
          2 ≤ active.card ∧ active.card ≤ 3 := by
        dsimp
        let active := Finset.univ.filter fun v : P.Vertex => 0 < x.val v
        obtain ⟨face,hFace,hOutside⟩ := x.property.2
        have hActiveFace : active ⊆ face := by
          intro v hv
          by_contra hnot
          have hz := hOutside v hnot
          have hp : 0 < x.val v := (Finset.mem_filter.mp hv).2
          rw [hz] at hp
          exact (lt_irrefl (0 : ℝ)) hp
        have hCarrier : x ∈ P.faceCarrier active := by
          intro v hv
          have hp : ¬ 0 < x.val v := by
            intro hp
            exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v,hp⟩)
          exact le_antisymm (le_of_not_gt hp) (x.property.1.1 v)
        have hLower : 2 ≤ active.card := by
          by_contra hn
          have hOne : active.card ≤ 1 := by omega
          obtain ⟨vertex,hVertex⟩ :=
            P.exists_eq_vertexPoint_of_mem_faceCarrier_of_card_le_one
              ⟨face,hFace⟩ hActiveFace hOne hCarrier
          exact hNoVertex vertex (by simpa only [realizationMap,Function.comp_apply,hVertex] using hx)
        exact ⟨hLower,(Finset.card_le_card hActiveFace).trans (P.faces_card face hFace).le⟩
      let BoundaryVertex := {e : Finset P.Vertex // e ∈ P.edges ∧ (e ∩ selected).Nonempty ∧ ¬ e ⊆ selected}
      let boundaryGraph : SimpleGraph BoundaryVertex := {
        Adj := fun x y => x ≠ y ∧ ∃ face ∈ P.faces, x.val ⊆ face ∧ y.val ⊆ face
        symm := ⟨by
          rintro x y ⟨hxy,face,hFace,hx,hy⟩
          exact ⟨hxy.symm,face,hFace,hy,hx⟩⟩
        loopless := ⟨fun x h => h.1 rfl⟩ }
      have hBoundaryGraph : boundaryGraph.IsCycles ∧
          ∀ v, (boundaryGraph.neighborSet v).Nonempty := by
        have hUnion (e f face : Finset P.Vertex) (he : e.card = 2) (hf : f.card = 2)
            (hFace : face.card = 3) (hne : e ≠ f) (hef : e ⊆ face) (hff : f ⊆ face) :
            e ∪ f = face := by
          have hnot : ¬ f ⊆ e := by
            intro h
            exact hne (Finset.eq_of_subset_of_card_le h (by omega)).symm
          obtain ⟨v,hvf,hve⟩ := Finset.not_subset.mp hnot
          have hProper : e ⊂ e ∪ f := Finset.ssubset_iff_subset_ne.mpr ⟨
            Finset.subset_union_left,by
              intro heq
              have hm : v ∈ e ∪ f := Finset.mem_union.mpr (Or.inr hvf)
              rw [← heq] at hm
              exact hve hm⟩
          have hlt := Finset.card_lt_card hProper
          exact Finset.eq_of_subset_of_card_le (Finset.union_subset hef hff) (by omega)
        have hTwoCuts (face : Finset P.Vertex) (hFace : face.card = 3)
            (hYes : (face ∩ selected).Nonempty) (hNo : ¬ face ⊆ selected) :
            ((face.powersetCard 2).filter fun e => (e ∩ selected).Nonempty ∧ ¬ e ⊆ selected).card = 2 := by
          obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hFace
          have hpc : ({c} : Finset P.Vertex).powerset = {∅,{c}} := by
            ext e
            simp only [Finset.mem_powerset,Finset.subset_singleton_iff,Finset.mem_insert,
              Finset.mem_singleton]
          have habac : ({a,b} : Finset P.Vertex) ≠ {a,c} := by
            intro h
            have hm : b ∈ ({a,c} : Finset P.Vertex) := h ▸ (by simp)
            simp_all
          have habbc : ({a,b} : Finset P.Vertex) ≠ {b,c} := by
            intro h
            have hm : a ∈ ({b,c} : Finset P.Vertex) := h ▸ (by simp)
            simp_all
          have hacbc : ({a,c} : Finset P.Vertex) ≠ {b,c} := by
            intro h
            have hm : a ∈ ({b,c} : Finset P.Vertex) := h ▸ (by simp)
            simp_all
          by_cases ha : a ∈ selected <;> by_cases hb : b ∈ selected <;> by_cases hc : c ∈ selected <;>
            simp_all [Finset.powersetCard_eq_filter,Finset.powerset_insert,hpc,Finset.insert_inter,
              Finset.filter_insert,Finset.filter_singleton,Finset.subset_iff]
        let cuts (face : Finset P.Vertex) :=
          (face.powersetCard 2).filter fun e => (e ∩ selected).Nonempty ∧ ¬ e ⊆ selected
        have other (x : BoundaryVertex) (face : Finset P.Vertex) (hFace : face ∈ P.faces)
            (hx : x.val ⊆ face) : ∃ y : BoundaryVertex, x ≠ y ∧ cuts face = {x.val,y.val} := by
          have hxMem : x.val ∈ cuts face := Finset.mem_filter.mpr ⟨
            Finset.mem_powersetCard.mpr ⟨hx,P.card_of_mem_edges x.property.1⟩,x.property.2⟩
          have hYes : (face ∩ selected).Nonempty := by
            obtain ⟨v,hv⟩ := x.property.2.1
            exact ⟨v,Finset.mem_inter.mpr ⟨hx (Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2⟩⟩
          have hNo : ¬ face ⊆ selected := fun h => x.property.2.2 (hx.trans h)
          have hCard : (cuts face).card = 2 := hTwoCuts face (P.faces_card face hFace) hYes hNo
          obtain ⟨a,b,hab,hPair⟩ := Finset.card_eq_two.mp hCard
          have hxAB : x.val = a ∨ x.val = b := by
            rw [hPair] at hxMem
            simpa only [Finset.mem_insert,Finset.mem_singleton] using hxMem
          have mkOther (y : Finset P.Vertex) (hy : y ∈ cuts face) (hne : x.val ≠ y)
              (hPair : cuts face = {x.val,y}) : ∃ y' : BoundaryVertex, x ≠ y' ∧ cuts face = {x.val,y'.val} := by
            have hyEdge : y ∈ P.edges := Finset.mem_biUnion.mpr ⟨face,hFace,(Finset.mem_filter.mp hy).1⟩
            let y' : BoundaryVertex := ⟨y,hyEdge,(Finset.mem_filter.mp hy).2⟩
            refine ⟨y',?_,hPair⟩
            exact fun heq => hne (congrArg Subtype.val heq)
          rcases hxAB with hxA | hxB
          · apply mkOther b
            · rw [hPair]; simp
            · exact hxA ▸ hab
            · simpa only [hxA] using hPair
          · apply mkOther a
            · rw [hPair]; simp
            · exact hxB ▸ hab.symm
            · simpa only [hxB,Finset.pair_comm] using hPair
        have hNeighbors (x : BoundaryVertex) : ∃ y z : BoundaryVertex, y ≠ z ∧ boundaryGraph.neighborSet x = {y,z} := by
          let incident := P.faces.filter fun face => x.val ⊆ face
          have hCard : incident.card = 2 := hValenceTwo ⟨x.val,x.property.1⟩ x.property.2.1 x.property.2.2
          obtain ⟨a,b,hab,hPair⟩ := Finset.card_eq_two.mp hCard
          have haI : a ∈ incident := by rw [hPair]; simp
          have hbI : b ∈ incident := by rw [hPair]; simp
          have haF := (Finset.mem_filter.mp haI).1
          have hbF := (Finset.mem_filter.mp hbI).1
          have hxa := (Finset.mem_filter.mp haI).2
          have hxb := (Finset.mem_filter.mp hbI).2
          obtain ⟨y,hxy,haCuts⟩ := other x a haF hxa
          obtain ⟨z,hxz,hbCuts⟩ := other x b hbF hxb
          have hyC : y.val ∈ cuts a := by rw [haCuts]; simp
          have hzC : z.val ∈ cuts b := by rw [hbCuts]; simp
          have hya : y.val ⊆ a := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hyC).1).1
          have hzb : z.val ⊆ b := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hzC).1).1
          have hyz : y ≠ z := by
            intro heq
            have hne : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
            have huA := hUnion x.val y.val a (P.card_of_mem_edges x.property.1)
              (P.card_of_mem_edges y.property.1) (P.faces_card a haF) hne hxa hya
            have huB := hUnion x.val y.val b (P.card_of_mem_edges x.property.1)
              (P.card_of_mem_edges y.property.1) (P.faces_card b hbF) hne hxb (heq ▸ hzb)
            exact hab (huA.symm.trans huB)
          refine ⟨y,z,hyz,?_⟩
          ext w
          change (x ≠ w ∧ ∃ face ∈ P.faces, x.val ⊆ face ∧ w.val ⊆ face) ↔ w ∈ ({y,z} : Set BoundaryVertex)
          constructor
          · rintro ⟨hxw,face,hFace,hxFace,hwFace⟩
            have hi : face ∈ incident := Finset.mem_filter.mpr ⟨hFace,hxFace⟩
            rw [hPair] at hi
            have hwCut : w.val ∈ cuts face := Finset.mem_filter.mpr ⟨
              Finset.mem_powersetCard.mpr ⟨hwFace,P.card_of_mem_edges w.property.1⟩,w.property.2⟩
            rcases Finset.mem_insert.mp hi with ha | hb
            · rw [ha,haCuts] at hwCut
              rcases Finset.mem_insert.mp hwCut with he | he
              · exact False.elim (hxw (Subtype.ext he.symm))
              · left
                exact Subtype.ext (Finset.mem_singleton.mp he)
            · have hb' : face = b := Finset.mem_singleton.mp hb
              rw [hb',hbCuts] at hwCut
              rcases Finset.mem_insert.mp hwCut with he | he
              · exact False.elim (hxw (Subtype.ext he.symm))
              · right
                exact Finset.mem_singleton.mp he |> Subtype.ext
          · intro hw
            rcases Set.mem_insert_iff.mp hw with hw | hw
            · subst w
              exact ⟨hxy,a,haF,hxa,hya⟩
            · have hw' : w = z := Set.mem_singleton_iff.mp hw
              subst w
              exact ⟨hxz,b,hbF,hxb,hzb⟩
        refine ⟨?_,?_⟩
        · intro x _
          obtain ⟨y,z,hyz,hEq⟩ := hNeighbors x
          rw [hEq]
          exact Set.ncard_pair hyz
        · intro x
          obtain ⟨y,z,hyz,hEq⟩ := hNeighbors x
          rw [hEq]
          exact ⟨y,Or.inl rfl⟩
      have hBoundaryCycles (v : BoundaryVertex) :
          ∃ p : boundaryGraph.Walk v v, p.IsCycle ∧
            p.toSubgraph.verts = (boundaryGraph.connectedComponentMk v).supp := by
        exact hBoundaryGraph.1.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
          (show v ∈ (boundaryGraph.connectedComponentMk v).supp from rfl)
          (hBoundaryGraph.2 v)
      have identifyCutMidpoint (P : IntrinsicTwoComplex) (selected : Finset P.Vertex)
          (x : P.realization) (hHalf : (∑ v ∈ selected, x.val v) = (1 : ℝ) / 2)
          (hTwo : (Finset.univ.filter fun v : P.Vertex => 0 < x.val v).card = 2) :
          ∃ e : P.Edge, (e.val ∩ selected).Nonempty ∧ ¬ e.val ⊆ selected ∧
            x = P.edgePath e ⟨1 / 2,by constructor <;> norm_num⟩ := by
        classical
        let active := Finset.univ.filter fun v : P.Vertex => 0 < x.val v
        have hZero (v : P.Vertex) (hv : v ∉ active) : x.val v = 0 := by
          have hp : ¬ 0 < x.val v := fun hp => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v,hp⟩)
          exact le_antisymm (le_of_not_gt hp) (x.property.1.1 v)
        have hSumActive : (∑ v ∈ active, x.val v) = 1 := by
          calc
            _ = ∑ v ∈ Finset.univ, x.val v := Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hZero v hv)
            _ = 1 := x.property.1.2
        obtain ⟨face,hFace,hOutside⟩ := x.property.2
        have hActiveFace : active ⊆ face := by
          intro v hv
          by_contra hn
          have hp : 0 < x.val v := (Finset.mem_filter.mp hv).2
          rw [hOutside v hn] at hp
          exact (lt_irrefl (0 : ℝ)) hp
        have hEdge : active ∈ P.edges := Finset.mem_biUnion.mpr ⟨face,hFace,
          Finset.mem_powersetCard.mpr ⟨hActiveFace,hTwo⟩⟩
        let e : P.Edge := ⟨active,hEdge⟩
        have hYes : (e.val ∩ selected).Nonempty := by
          have hp : 0 < ∑ v ∈ selected, x.val v := by rw [hHalf]; norm_num
          obtain ⟨v,hv,hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun v _ => x.property.1.1 v)).mp hp
          exact ⟨v,Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ v,hpos⟩,hv⟩⟩
        have hNo : ¬ e.val ⊆ selected := by
          intro h
          have he : (∑ v ∈ active, x.val v) = ∑ v ∈ selected, x.val v :=
            Finset.sum_subset h (fun v _ hv => hZero v hv)
          rw [hSumActive,hHalf] at he
          norm_num at he
        have habits : (P.edgeFirst e ∈ selected ∧ P.edgeSecond e ∉ selected) ∨
            (P.edgeSecond e ∈ selected ∧ P.edgeFirst e ∉ selected) := by
          rw [P.edge_eq_pair e] at hYes hNo
          simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff] at hNo
          by_cases ha : P.edgeFirst e ∈ selected
          · exact Or.inl ⟨ha,fun hb => hNo ⟨ha,hb⟩⟩
          · refine Or.inr ⟨?_,ha⟩
            obtain ⟨v,hv⟩ := hYes
            have hvpair := (Finset.mem_inter.mp hv).1
            have hvs := (Finset.mem_inter.mp hv).2
            simp only [Finset.mem_insert,Finset.mem_singleton] at hvpair
            rcases hvpair with rfl | rfl
            · exact False.elim (ha hvs)
            · exact hvs
        have hSumPair : x.val (P.edgeFirst e) + x.val (P.edgeSecond e) = 1 := by
          have hPair : active = {P.edgeFirst e,P.edgeSecond e} := P.edge_eq_pair e
          simpa only [hPair,Finset.sum_pair (P.edgeFirst_ne_edgeSecond e)] using hSumActive
        have hCoords : x.val (P.edgeFirst e) = 1 / 2 ∧ x.val (P.edgeSecond e) = 1 / 2 := by
          rcases habits with ⟨ha,hb⟩ | ⟨hb,ha⟩
          · have he : (∑ v ∈ selected, x.val v) = x.val (P.edgeFirst e) := by
              apply Finset.sum_eq_single
              · intro v hv hne
                apply hZero
                change v ∉ e.val
                rw [P.edge_eq_pair e]
                simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
                exact ⟨hne,fun heq => hb (heq ▸ hv)⟩
              · exact fun hn => False.elim (hn ha)
            constructor <;> linarith
          · have he : (∑ v ∈ selected, x.val v) = x.val (P.edgeSecond e) := by
              apply Finset.sum_eq_single
              · intro v hv hne
                apply hZero
                change v ∉ e.val
                rw [P.edge_eq_pair e]
                simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
                exact ⟨fun heq => ha (heq ▸ hv),hne⟩
              · exact fun hn => False.elim (hn hb)
            constructor <;> linarith
        refine ⟨e,hYes,hNo,?_⟩
        apply Subtype.ext
        funext v
        by_cases hvFirst : v = P.edgeFirst e
        · subst v
          rw [P.edgePath_apply_first,hCoords.1]
          norm_num
        by_cases hvSecond : v = P.edgeSecond e
        · subst v
          rw [P.edgePath_apply_second,hCoords.2]
        have hvNot : v ∉ e.val := by
          rw [P.edge_eq_pair e]
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
          exact ⟨hvFirst,hvSecond⟩
        have hm : P.edgePath e ⟨1/2,by constructor <;> norm_num⟩ ∈ P.faceCarrier e.val := by
          rw [← P.range_edgePath e]
          exact ⟨_,rfl⟩
        exact (hZero v hvNot).trans (hm v hvNot).symm
      have hFrontierCutVertex (x : P.realization)
          (hx : realizationMap x ∈ frontier N)
          (hTwo : (Finset.univ.filter fun v : P.Vertex => 0 < x.val v).card = 2) :
          ∃ v : BoundaryVertex, x = P.edgePath ⟨v.val,v.property.1⟩
            ⟨1 / 2,by constructor <;> norm_num⟩ := by
        obtain ⟨edge,hYes,hNo,hPoint⟩ :=
          identifyCutMidpoint P selected x (hFrontierLevel x hx) hTwo
        exact ⟨⟨edge.val,edge.property,hYes,hNo⟩,hPoint⟩
      have triangleCutPath (P : IntrinsicTwoComplex) (selected : Finset P.Vertex)
          (a b c : P.Vertex) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
          (hFace : ({a,b,c} : Finset P.Vertex) ∈ P.faces)
          (hColor : (a ∈ selected ∧ b ∉ selected ∧ c ∉ selected) ∨
            (a ∉ selected ∧ b ∈ selected ∧ c ∈ selected)) :
          ∃ f : C(unitInterval,P.realization), Topology.IsEmbedding f ∧
            (∀ t v, (f t).val v =
              if v = a then (1 : ℝ) / 2 else if v = b then (1 - t.val) / 2
              else if v = c then t.val / 2 else 0) ∧
            Set.range f = {x | x ∈ P.faceCarrier {a,b,c} ∧
              (∑ v ∈ selected,x.val v) = (1 : ℝ) / 2} := by
        classical
        let q (t : unitInterval) : P.Vertex → ℝ :=
          fun v => if v = a then 1/2 else if v = b then (1-t.val)/2
            else if v = c then t.val/2 else 0
        have hQa (t : unitInterval) : q t a = 1/2 := by simp [q]
        have hQb (t : unitInterval) : q t b = (1-t.val)/2 := by simp [q,hab.symm]
        have hQc (t : unitInterval) : q t c = t.val/2 := by simp [q,hac.symm,hbc.symm]
        have hQzero (t : unitInterval) (v : P.Vertex) (hv : v ∉ ({a,b,c} : Finset P.Vertex)) :
            q t v = 0 := by
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv
          simp [q,hv.1,hv.2.1,hv.2.2]
        have hQsum (t : unitInterval) : ∑ v, q t v = 1 := by
          calc
            _ = ∑ v ∈ ({a,b,c} : Finset P.Vertex), q t v :=
              (Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hQzero t v hv)).symm
            _ = 1 := by
              rw [Finset.sum_insert (by simp [hab,hac]),Finset.sum_pair hbc,hQa,hQb,hQc]
              ring
        let f : C(unitInterval,P.realization) := {
          toFun := fun t => ⟨q t,⟨by
            intro v
            dsimp [q]
            split_ifs
            · norm_num
            · exact div_nonneg (sub_nonneg.mpr t.property.2) (by norm_num)
            · exact div_nonneg t.property.1 (by norm_num)
            · exact le_refl 0,hQsum t⟩,⟨{a,b,c},hFace,hQzero t⟩⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            apply continuous_pi
            intro v
            dsimp [q]
            split_ifs <;> fun_prop }
        have hCoords (t : unitInterval) (v : P.Vertex) : (f t).val v = q t v := rfl
        have hEmbedding : Topology.IsEmbedding f := by
          apply (f.continuous.isClosedEmbedding ?_).isEmbedding
          intro t u h
          apply Subtype.ext
          have he := congrArg (fun x : P.realization => x.val c) h
          change q t c = q u c at he
          rw [hQc,hQc] at he
          linarith
        have hSumSelected (x : P.realization) (hCarrier : x ∈ P.faceCarrier {a,b,c}) :
            (∑ v ∈ selected,x.val v) =
              if a ∈ selected then x.val a else x.val b + x.val c := by
          rcases hColor with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
          · rw [if_pos ha]
            apply Finset.sum_eq_single
            · intro v hv hne
              apply hCarrier
              simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
              exact ⟨hne,fun he => hb (he ▸ hv),fun he => hc (he ▸ hv)⟩
            · exact fun hn => False.elim (hn ha)
          · rw [if_neg ha]
            calc
              _ = ∑ v ∈ ({b,c} : Finset P.Vertex),x.val v :=
                (Finset.sum_subset (by
                  intro v hv
                  have hv' : v = b ∨ v = c := by simpa using hv
                  rcases hv' with rfl | rfl
                  · exact hb
                  · exact hc) (by
                  intro v hv hn
                  apply hCarrier
                  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn ⊢
                  exact ⟨fun he => ha (he ▸ hv),hn.1,hn.2⟩)).symm
              _ = _ := Finset.sum_pair hbc
        refine ⟨f,hEmbedding,fun t v => rfl,?_⟩
        ext x
        constructor
        · rintro ⟨t,rfl⟩
          have hCarrier : f t ∈ P.faceCarrier {a,b,c} := hQzero t
          refine ⟨hCarrier,?_⟩
          rw [hSumSelected _ hCarrier]
          change (if a ∈ selected then q t a else q t b + q t c) = 1/2
          rw [hQa,hQb,hQc]
          split_ifs <;> ring
        · rintro ⟨hCarrier,hHalf⟩
          have hsum : x.val a + x.val b + x.val c = 1 := by
            have ht := x.property.1.2
            have he : (∑ v ∈ ({a,b,c} : Finset P.Vertex),x.val v) = ∑ v,x.val v :=
              Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hCarrier v hv)
            rw [Finset.sum_insert (by simp [hab,hac]),Finset.sum_pair hbc,ht] at he
            linarith
          have hxa : x.val a = 1/2 := by
            rw [hSumSelected _ hCarrier] at hHalf
            split_ifs at hHalf <;> linarith
          let t : unitInterval := ⟨2*x.val c,by
            constructor
            · exact mul_nonneg (by norm_num) (x.property.1.1 c)
            · linarith [x.property.1.1 b]⟩
          refine ⟨t,?_⟩
          apply Subtype.ext
          funext v
          change q t v = x.val v
          by_cases hva : v = a
          · subst v; rw [hQa,hxa]
          by_cases hvb : v = b
          · subst v; rw [hQb]; dsimp [t]; linarith
          by_cases hvc : v = c
          · subst v; rw [hQc]; dsimp [t]; ring
          have hn : v ∉ ({a,b,c} : Finset P.Vertex) := by
            simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
            exact ⟨hva,hvb,hvc⟩
          exact (hQzero t v hn).trans (hCarrier v hn).symm

      have triangleColor {V : Type} [DecidableEq V] (selected face : Finset V)
          (hcard : face.card = 3) (hYes : (face ∩ selected).Nonempty)
          (hNo : ¬ face ⊆ selected) :
          ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ face = {a,b,c} ∧
            ((a ∈ selected ∧ b ∉ selected ∧ c ∉ selected) ∨
             (a ∉ selected ∧ b ∈ selected ∧ c ∈ selected)) := by
        obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hcard
        by_cases ha : a ∈ selected <;> by_cases hb : b ∈ selected <;> by_cases hc : c ∈ selected
        · apply False.elim
          apply hNo
          intro v hv
          have hv' : v = a ∨ v = b ∨ v = c := by simpa using hv
          rcases hv' with rfl | rfl | rfl
          · exact ha
          · exact hb
          · exact hc
        · refine ⟨c,a,b,hac.symm,hbc.symm,hab,?_,Or.inr ⟨hc,ha,hb⟩⟩
          ext v; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
        · refine ⟨b,a,c,hab.symm,hbc,hac,?_,Or.inr ⟨hb,ha,hc⟩⟩
          ext v; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
        · exact ⟨a,b,c,hab,hac,hbc,rfl,Or.inl ⟨ha,hb,hc⟩⟩
        · exact ⟨a,b,c,hab,hac,hbc,rfl,Or.inr ⟨ha,hb,hc⟩⟩
        · refine ⟨b,a,c,hab.symm,hbc,hac,?_,Or.inl ⟨hb,ha,hc⟩⟩
          ext v; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
        · refine ⟨c,a,b,hac.symm,hbc.symm,hab,?_,Or.inl ⟨hc,ha,hb⟩⟩
          ext v; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
        · obtain ⟨v,hv⟩ := hYes
          simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton] at hv
          have hm := hv.2
          rcases hv.1 with rfl | rfl | rfl
          · exact (ha hm).elim
          · exact (hb hm).elim
          · exact (hc hm).elim

      have halfLevelMixed (P : IntrinsicTwoComplex) (selected face : Finset P.Vertex)
          (x : P.realization) (hCarrier : x ∈ P.faceCarrier face)
          (hHalf : (∑ v ∈ selected,x.val v) = (1 : ℝ) / 2) :
          (face ∩ selected).Nonempty ∧ ¬ face ⊆ selected := by
        constructor
        · by_contra hn
          have hz : (∑ v ∈ selected,x.val v) = 0 := by
            apply Finset.sum_eq_zero
            intro v hv
            apply hCarrier
            intro hf
            exact hn ⟨v,Finset.mem_inter.mpr ⟨hf,hv⟩⟩
          linarith
        · intro hs
          have hone : (∑ v ∈ selected,x.val v) = 1 := by
            calc
              _ = ∑ v,x.val v := Finset.sum_subset (Finset.subset_univ _) (by
                intro v _ hv
                apply hCarrier
                exact fun hf => hv (hs hf))
              _ = 1 := x.property.1.2
          linarith

      have hActualMixedTriangleArc (face : Finset P.Vertex) (hFace : face ∈ P.faces)
          (hYes : (face ∩ selected).Nonempty) (hNo : ¬ face ⊆ selected) :
          ∃ f : C(unitInterval,P.realization), Topology.IsEmbedding f ∧
            Set.range f = {x | x ∈ P.faceCarrier face ∧
              (∑ v ∈ selected,x.val v) = (1 : ℝ) / 2} := by
        obtain ⟨a,b,c,hab,hac,hbc,hOrder,hColor⟩ :=
          triangleColor selected face (P.faces_card face hFace) hYes hNo
        obtain ⟨f,hf,hCoords,hRange⟩ := triangleCutPath P selected a b c hab hac hbc
          (hOrder ▸ hFace) hColor
        refine ⟨f,hf,?_⟩
        simpa only [hOrder] using hRange
      have hActualFrontierArc (x : P.realization)
          (hx : realizationMap x ∈ frontier N) :
          ∃ face ∈ P.faces, ∃ f : C(unitInterval,P.realization),
            Topology.IsEmbedding f ∧
            Set.range f = {y | y ∈ P.faceCarrier face ∧
              (∑ v ∈ selected,y.val v) = (1 : ℝ) / 2} ∧ x ∈ Set.range f := by
        obtain ⟨face,hFace,hOutside⟩ := x.property.2
        have hCarrier : x ∈ P.faceCarrier face := hOutside
        have hHalf := hFrontierLevel x hx
        obtain ⟨hYes,hNo⟩ := halfLevelMixed P selected face x hCarrier hHalf
        obtain ⟨f,hf,hRange⟩ := hActualMixedTriangleArc face hFace hYes hNo
        refine ⟨face,hFace,f,hf,hRange,?_⟩
        rw [hRange]
        exact ⟨hCarrier,hHalf⟩
      have triangleInteriorSupport (P : IntrinsicTwoComplex) (a b c : P.Vertex)
          (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
          (f : C(unitInterval,P.realization))
          (hCoords : ∀ t v, (f t).val v =
            if v = a then (1 : ℝ)/2 else if v = b then (1-t.val)/2
            else if v = c then t.val/2 else 0)
          (t : unitInterval) (ht : t ∈ Set.Ioo 0 1) :
          (Finset.univ.filter fun v : P.Vertex => 0 < (f t).val v) = {a,b,c} := by
        ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
        rw [hCoords]
        have ht0 : 0 < t.val := ht.1
        have ht1 : t.val < 1 := ht.2
        by_cases ha : v = a
        · simp [ha]
        by_cases hb : v = b
        · have hp : 0 < (1-t.val)/2 := div_pos (sub_pos.mpr ht1) (by norm_num)
          simpa only [hb,hab.symm,ite_false,ite_true,eq_self,or_true,true_or,iff_true] using hp
        by_cases hc : v = c
        · have hp : 0 < t.val/2 := div_pos ht0 (by norm_num)
          simpa only [hc,hac.symm,hbc.symm,ite_false,ite_true,eq_self,or_true,true_or,iff_true] using hp
        simp [ha,hb,hc]

      have fullSupportUniqueFace (P : IntrinsicTwoComplex) (face face' : Finset P.Vertex)
          (hFace : face ∈ P.faces) (hFace' : face' ∈ P.faces)
          (x : P.realization) (hCarrier : x ∈ P.faceCarrier face)
          (hCarrier' : x ∈ P.faceCarrier face')
          (hThree : (Finset.univ.filter fun v : P.Vertex => 0 < x.val v).card = 3) :
          face = face' := by
        let active := Finset.univ.filter fun v : P.Vertex => 0 < x.val v
        have ha (f : Finset P.Vertex) (hf : x ∈ P.faceCarrier f) : active ⊆ f := by
          intro v hv
          by_contra hn
          have hp := (Finset.mem_filter.mp hv).2
          rw [hf v hn] at hp
          exact (lt_irrefl (0 : ℝ)) hp
        have hEq : active = face := Finset.eq_of_subset_of_card_le (ha face hCarrier)
          (by rw [P.faces_card face hFace]; exact hThree.ge)
        have hEq' : active = face' := Finset.eq_of_subset_of_card_le (ha face' hCarrier')
          (by rw [P.faces_card face' hFace']; exact hThree.ge)
        exact hEq.symm.trans hEq'

      have triangleEndpointSupport (P : IntrinsicTwoComplex) (a b c : P.Vertex)
          (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
          (f : C(unitInterval,P.realization))
          (hCoords : ∀ t v, (f t).val v =
            if v = a then (1 : ℝ)/2 else if v = b then (1-t.val)/2
            else if v = c then t.val/2 else 0) :
          (Finset.univ.filter fun v : P.Vertex => 0 < (f 0).val v).card = 2 ∧
          (Finset.univ.filter fun v : P.Vertex => 0 < (f 1).val v).card = 2 := by
        have h0 : (Finset.univ.filter fun v : P.Vertex => 0 < (f 0).val v) = {a,b} := by
          ext v
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
          rw [hCoords]
          by_cases ha : v = a
          · simp [ha]
          by_cases hb : v = b
          · simp [hb,hab.symm]
          simp [ha,hb]
        have h1 : (Finset.univ.filter fun v : P.Vertex => 0 < (f 1).val v) = {a,c} := by
          ext v
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
          rw [hCoords]
          by_cases ha : v = a
          · simp [ha]
          by_cases hb : v = b
          · simp [hb,hab.symm,hbc]
          by_cases hc : v = c
          · simp [hc,hac.symm,hbc.symm]
          simp [ha,hb,hc]
        rw [h0,h1]
        simp [hab,hac]

      have cutPositionInjective (P : IntrinsicTwoComplex) : Function.Injective
          (fun e : P.Edge => P.edgePath e ⟨1/2,by constructor <;> norm_num⟩) := by
        intro e d h
        by_contra hn
        have hdis := P.disjoint_edgePath_image_Ioo hn
        exact Set.disjoint_left.mp hdis
          ⟨⟨1/2,by constructor <;> norm_num⟩,by constructor <;> norm_num,rfl⟩
          ⟨⟨1/2,by constructor <;> norm_num⟩,by constructor <;> norm_num,h.symm⟩

      have cutMidpointFaceSubset (P : IntrinsicTwoComplex) (e : P.Edge) (face : Finset P.Vertex)
          (hCarrier : P.edgePath e ⟨1/2,by constructor <;> norm_num⟩ ∈ P.faceCarrier face) :
          e.val ⊆ face := by
        intro v hv
        by_contra hn
        have hz := hCarrier v hn
        rw [P.edge_eq_pair e] at hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · rw [P.edgePath_apply_first] at hz
          norm_num at hz
        · rw [P.edgePath_apply_second] at hz
          norm_num at hz
      have hActualMatchedTriangleArc (face : Finset P.Vertex) (hFace : face ∈ P.faces)
          (hYes : (face ∩ selected).Nonempty) (hNo : ¬ face ⊆ selected) :
          ∃ f : C(unitInterval,P.realization), Topology.IsEmbedding f ∧
            Set.range f = {x | x ∈ P.faceCarrier face ∧
              (∑ v ∈ selected,x.val v) = (1 : ℝ)/2} ∧
            ∃ u v : BoundaryVertex,
              f 0 = P.edgePath ⟨u.val,u.property.1⟩ ⟨1/2,by constructor <;> norm_num⟩ ∧
              f 1 = P.edgePath ⟨v.val,v.property.1⟩ ⟨1/2,by constructor <;> norm_num⟩ ∧
              boundaryGraph.Adj u v ∧ ∀ t ∈ Set.Ioo (0 : unitInterval) 1,
                (Finset.univ.filter fun z : P.Vertex => 0 < (f t).val z).card = 3 := by
        obtain ⟨a,b,c,hab,hac,hbc,hOrder,hColor⟩ :=
          triangleColor selected face (P.faces_card face hFace) hYes hNo
        obtain ⟨f,hf,hCoords,hRange⟩ := triangleCutPath P selected a b c hab hac hbc
          (hOrder ▸ hFace) hColor
        have hRange' : Set.range f = {x | x ∈ P.faceCarrier face ∧
            (∑ v ∈ selected,x.val v) = (1 : ℝ)/2} := by
          simpa only [hOrder] using hRange
        have hEndpoints := triangleEndpointSupport P a b c hab hac hbc f hCoords
        have hAt0 : f 0 ∈ Set.range f := ⟨0,rfl⟩
        have hAt1 : f 1 ∈ Set.range f := ⟨1,rfl⟩
        rw [hRange'] at hAt0 hAt1
        obtain ⟨e,heYes,heNo,he⟩ := identifyCutMidpoint P selected (f 0) hAt0.2 hEndpoints.1
        obtain ⟨d,hdYes,hdNo,hd⟩ := identifyCutMidpoint P selected (f 1) hAt1.2 hEndpoints.2
        let u : BoundaryVertex := ⟨e.val,e.property,heYes,heNo⟩
        let v : BoundaryVertex := ⟨d.val,d.property,hdYes,hdNo⟩
        refine ⟨f,hf,hRange',u,v,he,hd,?_,?_⟩
        · have hneq : u ≠ v := by
            intro huv
            have hpos : f 0 = f 1 := he.trans ((congrArg
              (fun w : BoundaryVertex => P.edgePath ⟨w.val,w.property.1⟩
                ⟨1/2,by constructor <;> norm_num⟩) huv).trans hd.symm)
            have h01 := congrArg Subtype.val (hf.injective hpos)
            norm_num at h01
          refine ⟨hneq,face,hFace,?_,?_⟩
          · exact cutMidpointFaceSubset P e face (he ▸ hAt0.1)
          · exact cutMidpointFaceSubset P d face (hd ▸ hAt1.1)
        · intro t ht
          rw [triangleInteriorSupport P a b c hab hac hbc f hCoords t ht]
          simp [hab,hac,hbc]
      have hTwoCuts (face : Finset P.Vertex) (hFace : face.card = 3)
          (hYes : (face ∩ selected).Nonempty) (hNo : ¬ face ⊆ selected) :
          ((face.powersetCard 2).filter fun e => (e ∩ selected).Nonempty ∧ ¬ e ⊆ selected).card = 2 := by
        clear hActualFrontierArc hActualMixedTriangleArc hFrontierCutVertex
          hBoundaryCycles hBoundaryGraph
        clear hActualMatchedTriangleArc boundaryGraph BoundaryVertex identifyCutMidpoint
          triangleCutPath halfLevelMixed triangleInteriorSupport fullSupportUniqueFace
          triangleEndpointSupport cutPositionInjective cutMidpointFaceSubset
        obtain ⟨a,b,c,hab,hac,hbc,rfl,hColor⟩ := triangleColor selected face hFace hYes hNo
        have hpc : ({c} : Finset P.Vertex).powerset = {∅,{c}} := by
          ext e
          simp only [Finset.mem_powerset,Finset.subset_singleton_iff,Finset.mem_insert,
            Finset.mem_singleton]
        have habac : ({a,b} : Finset P.Vertex) ≠ {a,c} := by
          intro h
          have hm : b ∈ ({a,c} : Finset P.Vertex) := h ▸ (by simp)
          simp_all
        have habbc : ({a,b} : Finset P.Vertex) ≠ {b,c} := by
          intro h
          have hm : a ∈ ({b,c} : Finset P.Vertex) := h ▸ (by simp)
          simp_all
        have hacbc : ({a,c} : Finset P.Vertex) ≠ {b,c} := by
          intro h
          have hm : a ∈ ({b,c} : Finset P.Vertex) := h ▸ (by simp)
          simp_all
        rcases hColor with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩ <;>
          simp_all [Finset.powersetCard_eq_filter,Finset.powerset_insert,hpc,Finset.insert_inter,
            Finset.filter_insert,Finset.filter_singleton,Finset.subset_iff]
      let position (v : BoundaryVertex) : P.realization :=
        P.edgePath ⟨v.val,v.property.1⟩ ⟨1/2,by constructor <;> norm_num⟩
      have hDirectedEdgeArc (x y : BoundaryVertex) (hAdj : boundaryGraph.Adj x y) :
          ∃ face ∈ P.faces, ∃ f : Path (position x) (position y), Topology.IsEmbedding f ∧
            Set.range f = {z | z ∈ P.faceCarrier face ∧
              (∑ v ∈ selected,z.val v) = (1 : ℝ)/2} ∧
            ∀ t ∈ Set.Ioo (0 : unitInterval) 1,
              (Finset.univ.filter fun z : P.Vertex => 0 < (f t).val z).card = 3 := by
        obtain ⟨hne,face,hFace,hx,hy⟩ := hAdj
        have hYes : (face ∩ selected).Nonempty := by
          obtain ⟨v,hv⟩ := x.property.2.1
          exact ⟨v,Finset.mem_inter.mpr ⟨hx (Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2⟩⟩
        have hNo : ¬ face ⊆ selected := fun h => x.property.2.2 (hx.trans h)
        obtain ⟨f,hf,hRange,u,v,hu,hv,hUV,hInterior⟩ := hActualMatchedTriangleArc face hFace hYes hNo
        let cuts := (face.powersetCard 2).filter fun e => (e ∩ selected).Nonempty ∧ ¬ e ⊆ selected
        have hCard : cuts.card = 2 := hTwoCuts face (P.faces_card face hFace) hYes hNo
        have hMem (z : BoundaryVertex) (hz : z.val ⊆ face) : z.val ∈ cuts :=
          Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hz,P.card_of_mem_edges z.property.1⟩,z.property.2⟩
        have hxy : x.val ≠ y.val := fun h => hne (Subtype.ext h)
        have hSub : ({x.val,y.val} : Finset (Finset P.Vertex)) ⊆ cuts := by
          intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact hMem x hx
          · rw [Finset.mem_singleton] at he
            subst e
            exact hMem y hy
        have hXY : ({x.val,y.val} : Finset (Finset P.Vertex)) = cuts :=
          Finset.eq_of_subset_of_card_le hSub (by rw [hCard]; simp [hxy])
        have hAt0 : f 0 ∈ Set.range f := ⟨0,rfl⟩
        have hAt1 : f 1 ∈ Set.range f := ⟨1,rfl⟩
        rw [hRange] at hAt0 hAt1
        have huFace : u.val ⊆ face := cutMidpointFaceSubset P ⟨u.val,u.property.1⟩ face (hu ▸ hAt0.1)
        have hvFace : v.val ⊆ face := cutMidpointFaceSubset P ⟨v.val,v.property.1⟩ face (hv ▸ hAt1.1)
        have huChoice : u = x ∨ u = y := by
          have hm := hMem u huFace
          rw [← hXY] at hm
          simp only [Finset.mem_insert,Finset.mem_singleton] at hm
          exact hm.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
        have hvChoice : v = x ∨ v = y := by
          have hm := hMem v hvFace
          rw [← hXY] at hm
          simp only [Finset.mem_insert,Finset.mem_singleton] at hm
          exact hm.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
        let p : Path (position u) (position v) := {
          toFun := f, continuous_toFun := f.continuous, source' := hu, target' := hv }
        have hp : Topology.IsEmbedding p := hf
        rcases huChoice with rfl | rfl <;> rcases hvChoice with rfl | rfl
        · exact (hUV.1 rfl).elim
        · exact ⟨face,hFace,p,hp,hRange,hInterior⟩
        · refine ⟨face,hFace,p.symm,?_,?_,?_⟩
          · exact hp.comp unitInterval.symmHomeomorph.isEmbedding
          · rw [Path.symm_range]
            exact hRange
          · intro t ht
            have hs : unitInterval.symm t ∈ Set.Ioo (0 : unitInterval) 1 := by
              constructor
              · change 0 < 1-t.val
                have ht1 : t.val < 1 := ht.2
                linarith
              · change 1-t.val < 1
                have ht0 : 0 < t.val := ht.1
                linarith
            exact hInterior (unitInterval.symm t) hs
        · exact (hUV.1 rfl).elim
      let boundaryFace {x y : BoundaryVertex} (h : boundaryGraph.Adj x y) : Finset P.Vertex :=
        Classical.choose (hDirectedEdgeArc x y h)
      let boundaryArc {x y : BoundaryVertex} (h : boundaryGraph.Adj x y) :
          Path (position x) (position y) :=
        Classical.choose (Classical.choose_spec (hDirectedEdgeArc x y h)).2
      have hBoundaryArc {x y : BoundaryVertex} (h : boundaryGraph.Adj x y) :
          boundaryFace h ∈ P.faces ∧ Topology.IsEmbedding (boundaryArc h) ∧
            Set.range (boundaryArc h) = {z | z ∈ P.faceCarrier (boundaryFace h) ∧
              (∑ v ∈ selected,z.val v) = (1 : ℝ)/2} ∧
            ∀ t ∈ Set.Ioo (0 : unitInterval) 1,
              (Finset.univ.filter fun z : P.Vertex => 0 < (boundaryArc h t).val z).card = 3 := by
        exact ⟨(Classical.choose_spec (hDirectedEdgeArc x y h)).1,
          Classical.choose_spec (Classical.choose_spec (hDirectedEdgeArc x y h)).2⟩
      have hDistinctBoundaryArcFaces {x y z w : BoundaryVertex}
          (hxy : boundaryGraph.Adj x y) (hzw : boundaryGraph.Adj z w)
          (hne : boundaryFace hxy ≠ boundaryFace hzw)
          (t : unitInterval) (ht : t ∈ Set.Ioo 0 1) (r : unitInterval) :
          boundaryArc hxy t ≠ boundaryArc hzw r := by
        intro he
        obtain ⟨hf,hEmb,hRange,hInterior⟩ := hBoundaryArc hxy
        obtain ⟨hf',hEmb',hRange',hInterior'⟩ := hBoundaryArc hzw
        have hAt : boundaryArc hxy t ∈ Set.range (boundaryArc hxy) := ⟨t,rfl⟩
        have hAt' : boundaryArc hzw r ∈ Set.range (boundaryArc hzw) := ⟨r,rfl⟩
        rw [hRange] at hAt
        rw [hRange'] at hAt'
        exact hne (fullSupportUniqueFace P _ _ hf hf' _ hAt.1
          (he.symm ▸ hAt'.1) (hInterior t ht))
      have halfLevelOutsideInterior (P : IntrinsicTwoComplex) (selected face : Finset P.Vertex)
          (hFace : face ∈ P.faces) (x : P.realization)
          (hCarrier : x ∈ P.faceCarrier face) (w : P.Vertex)
          (hwFace : w ∈ face) (hw : w ∉ selected)
          (hHalf : (∑ v ∈ selected,x.val v) = (1 : ℝ)/2) :
          x ∉ interior {y : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ selected,y.val v} := by
        classical
        let vertex : P.realization := P.vertexPoint ⟨w,face,hFace,hwFace⟩
        have hvCarrier : vertex ∈ P.faceCarrier face :=
          (P.vertexPoint_mem_faceCarrier_iff _ _).mpr hwFace
        let q : C(unitInterval,P.realization) := {
          toFun := fun t => ⟨AffineMap.lineMap x.val vertex.val t.val,
            (convex_stdSimplex ℝ P.Vertex).lineMap_mem x.property.1 vertex.property.1 t.property,
            ⟨face,hFace,by
              intro v hv
              simp [AffineMap.lineMap_apply_module,hCarrier v hv,hvCarrier v hv]⟩⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            fun_prop }
        have hq0 : q 0 = x := by
          apply Subtype.ext
          simp [q,AffineMap.lineMap_apply_module]
        have hVertexSum : (∑ v ∈ selected,vertex.val v) = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          have hvw : v ≠ w := fun he => hw (he ▸ hv)
          change (Pi.single (M := fun _ : P.Vertex => ℝ) w (1 : ℝ)) v = 0
          simp [hvw]
        have hqSum (t : unitInterval) :
            (∑ v ∈ selected,(q t).val v) = (1-t.val)/2 := by
          change (∑ v ∈ selected,(AffineMap.lineMap x.val vertex.val t.val) v) = _
          simp only [AffineMap.lineMap_apply_module,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
          rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hHalf,hVertexSum]
          ring
        let times (n : ℕ) : unitInterval := ⟨(1/2 : ℝ)^n,by
          constructor
          · positivity
          · exact pow_le_one₀ (by norm_num) (by norm_num)⟩
        have htlim : Filter.Tendsto times Filter.atTop (𝓝 (0 : unitInterval)) := by
          apply tendsto_subtype_rng.mpr
          exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        have hlim : Filter.Tendsto (fun n => q (times n)) Filter.atTop (𝓝 x) := by
          rw [← hq0]
          exact q.continuous.continuousAt.tendsto.comp htlim
        have hOutside (n : ℕ) : q (times n) ∉
            {y : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ selected,y.val v} := by
          intro hn
          change (1 : ℝ)/2 ≤ ∑ v ∈ selected,(q (times n)).val v at hn
          rw [hqSum] at hn
          have hp : 0 < (times n).val := pow_pos (by norm_num) n
          linarith
        have hxClosure : x ∈ closure ({y : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ selected,y.val v}ᶜ) :=
          mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hOutside)
        simpa only [closure_compl,Set.mem_compl_iff] using hxClosure
      let B : Set P.realization := {x | (1 : ℝ)/2 ≤ ∑ v ∈ selected,x.val v}
      have hRefinedImage : N = realizationMap '' B := by
        ext y
        constructor
        · intro hy
          rw [hAImage] at hy
          obtain ⟨x,hx,rfl⟩ := hy
          refine ⟨R.homeo.symm x,?_,?_⟩
          · exact hx
          · simp [realizationMap]
        · rintro ⟨x,hx,rfl⟩
          rw [hAImage]
          refine ⟨R.homeo x,?_,rfl⟩
          change (1 : ℝ)/2 ≤ cutoff (R.homeo x)
          simpa only [B,Set.mem_setOf_eq,cutoff,R.homeo.symm_apply_apply] using hx
      have hRealizationRange : Set.range realizationMap = T.support := by
        change Set.range realizationMap = Set.range T.embed
        ext y
        constructor
        · rintro ⟨x,rfl⟩
          exact ⟨R.homeo x,rfl⟩
        · rintro ⟨x,rfl⟩
          refine ⟨R.homeo.symm x,?_⟩
          simp [realizationMap]
      have hActualHalfInterior : ∀ x : P.realization,
          (1 : ℝ)/2 ≤ ∑ v ∈ selected,x.val v →
            realizationMap x ∈ interior (Set.range realizationMap) := by
        intro x hx
        rw [hRealizationRange]
        apply hNSupport
        rw [hRefinedImage]
        exact ⟨x,hx,rfl⟩
      obtain ⟨actualHalfCharts,hActualHalfManifold⟩ :=
        actual_half_level_neighborhood_is_surface_with_boundary
          P selected realizationMap hRealizationEmbedding hActualHalfInterior
      letI : ChartedSpace (EuclideanHalfSpace 2) B := actualHalfCharts
      let actualHalfHomeomorph : B ≃ₜ N :=
        (hRealizationEmbedding.homeomorphImage B).trans
          (Homeomorph.setCongr hRefinedImage.symm)
      letI : ChartedSpace (EuclideanHalfSpace 2) N := actualHalfHomeomorph.chartedSpace
      letI : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 N := inferInstance
      have hPullInterior : realizationMap ⁻¹' interior N ⊆ interior B := by
        have hOpen : IsOpen (realizationMap ⁻¹' interior N) :=
          isOpen_interior.preimage hRealizationEmbedding.continuous
        apply hOpen.subset_interior_iff.mpr
        intro x hx
        have hxN : realizationMap x ∈ N := interior_subset hx
        rw [hRefinedImage] at hxN
        obtain ⟨z,hz,he⟩ := hxN
        have hzEq : z = x := hRealizationEmbedding.injective he
        simpa only [hzEq] using hz
      have hActualHalfFrontier (x : P.realization)
          (hHalf : (∑ v ∈ selected,x.val v) = (1 : ℝ)/2) :
          realizationMap x ∈ frontier N := by
        obtain ⟨face,hFace,hOutside⟩ := x.property.2
        have hCarrier : x ∈ P.faceCarrier face := hOutside
        obtain ⟨hYes,hNo⟩ := halfLevelMixed P selected face x hCarrier hHalf
        obtain ⟨v,hvf,hvn⟩ := Finset.not_subset.mp hNo
        have hNot : x ∉ interior B :=
          halfLevelOutsideInterior P selected face hFace x hCarrier v hvf hvn hHalf
        have hxN : realizationMap x ∈ N := by
          rw [hRefinedImage]
          exact ⟨x,by change (1 : ℝ)/2 ≤ ∑ v ∈ selected,x.val v; exact hHalf.ge,rfl⟩
        have hxNot : realizationMap x ∉ interior N := fun h => hNot (hPullInterior h)
        rw [frontier,hNCompact.isClosed.closure_eq]
        exact ⟨hxN,hxNot⟩
      have hBoundaryArcAvoidsOriginalK {x y : BoundaryVertex}
          (h : boundaryGraph.Adj x y) :
          Set.range (realizationMap ∘ boundaryArc h) ⊆ Kᶜ := by
        rintro z ⟨t,rfl⟩ hzK
        have hRange := (hBoundaryArc h).2.2.1
        have hAt : boundaryArc h t ∈ Set.range (boundaryArc h) := ⟨t,rfl⟩
        rw [hRange] at hAt
        have hFront := hActualHalfFrontier (boundaryArc h t) hAt.2
        exact hFront.2 (hOriginalK hzK)
      have midpointSupport (P : IntrinsicTwoComplex) (e : P.Edge) :
          (Finset.univ.filter fun v : P.Vertex =>
            0 < (P.edgePath e ⟨1/2,by constructor <;> norm_num⟩).val v) = e.val := by
        ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hp
          by_contra hn
          have hCarrier : P.edgePath e ⟨1/2,by constructor <;> norm_num⟩ ∈ P.faceCarrier e.val := by
            rw [← P.range_edgePath e]
            exact ⟨_,rfl⟩
          rw [hCarrier v hn] at hp
          exact (lt_irrefl (0 : ℝ)) hp
        · intro hv
          rw [P.edge_eq_pair e] at hv
          simp only [Finset.mem_insert,Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · rw [P.edgePath_apply_first]
            norm_num
          · rw [P.edgePath_apply_second]
            norm_num
      have hPositionSupport (v : BoundaryVertex) :
          (Finset.univ.filter fun z : P.Vertex => 0 < (position v).val z) = v.val :=
        midpointSupport P ⟨v.val,v.property.1⟩
      have hPositionInjective : Function.Injective position := by
        intro x y h
        have he : (⟨x.val,x.property.1⟩ : P.Edge) = ⟨y.val,y.property.1⟩ := cutPositionInjective P h
        exact Subtype.ext (congrArg (fun e : P.Edge => e.val) he)
      have hArcInteriorAvoidsVertices {x y : BoundaryVertex} (h : boundaryGraph.Adj x y)
          (t : unitInterval) (ht : t ∈ Set.Ioo 0 1) (v : BoundaryVertex) :
          boundaryArc h t ≠ position v := by
        intro he
        have hc := (hBoundaryArc h).2.2.2 t ht
        rw [he,hPositionSupport] at hc
        have hc2 := P.card_of_mem_edges v.property.1
        omega
      have hBoundaryFaceCuts {x y : BoundaryVertex} (h : boundaryGraph.Adj x y) :
          ((boundaryFace h).powersetCard 2).filter
            (fun e => (e ∩ selected).Nonempty ∧ ¬ e ⊆ selected) = {x.val,y.val} := by
        let face := boundaryFace h
        let cuts := (face.powersetCard 2).filter fun e => (e ∩ selected).Nonempty ∧ ¬ e ⊆ selected
        have hRange := (hBoundaryArc h).2.2.1
        have hAt0 : boundaryArc h 0 ∈ Set.range (boundaryArc h) := ⟨0,rfl⟩
        have hAt1 : boundaryArc h 1 ∈ Set.range (boundaryArc h) := ⟨1,rfl⟩
        rw [hRange] at hAt0 hAt1
        obtain ⟨hYes,hNo⟩ := halfLevelMixed P selected face (boundaryArc h 0) hAt0.1 hAt0.2
        have hCard : cuts.card = 2 := hTwoCuts face (P.faces_card face (hBoundaryArc h).1) hYes hNo
        have hxCarrier : position x ∈ P.faceCarrier face := by simpa only [Path.source] using hAt0.1
        have hyCarrier : position y ∈ P.faceCarrier face := by simpa only [Path.target] using hAt1.1
        have hxFace : x.val ⊆ face := cutMidpointFaceSubset P ⟨x.val,x.property.1⟩ face hxCarrier
        have hyFace : y.val ⊆ face := cutMidpointFaceSubset P ⟨y.val,y.property.1⟩ face hyCarrier
        have hMem (z : BoundaryVertex) (hz : z.val ⊆ face) : z.val ∈ cuts :=
          Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hz,P.card_of_mem_edges z.property.1⟩,z.property.2⟩
        have hSub : ({x.val,y.val} : Finset (Finset P.Vertex)) ⊆ cuts := by
          intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact hMem x hxFace
          · rw [Finset.mem_singleton] at he
            subst e
            exact hMem y hyFace
        have hxy : x.val ≠ y.val := fun he => h.1 (Subtype.ext he)
        exact (Finset.eq_of_subset_of_card_le hSub (by rw [hCard]; simp [hxy])).symm
      have hBoundaryFaceDistinct {x y z w : BoundaryVertex}
          (hxy : boundaryGraph.Adj x y) (hzw : boundaryGraph.Adj z w)
          (hne : ({x,y} : Finset BoundaryVertex) ≠ {z,w}) : boundaryFace hxy ≠ boundaryFace hzw := by
        intro he
        have hp := hBoundaryFaceCuts hxy
        have hp' := hBoundaryFaceCuts hzw
        rw [← he] at hp'
        have hvPair : ({x.val,y.val} : Finset (Finset P.Vertex)) = {z.val,w.val} := hp.symm.trans hp'
        have hImage : ({x,y} : Finset BoundaryVertex).image Subtype.val =
            ({z,w} : Finset BoundaryVertex).image Subtype.val := by
          simpa only [Finset.image_insert,Finset.image_singleton] using hvPair
        exact hne (Finset.image_injective Subtype.val_injective hImage)
      have hProperTime (t : unitInterval) (h0 : t ≠ 0) (h1 : t ≠ 1) : t ∈ Set.Ioo 0 1 := by
        constructor
        · change (0 : ℝ) < t.val
          exact lt_of_le_of_ne t.property.1 (fun he => h0 (Subtype.ext he.symm))
        · change t.val < (1 : ℝ)
          exact lt_of_le_of_ne t.property.2 (fun he => h1 (Subtype.ext he))
      have hArcMeetOnlyGraphVertices {x y z w : BoundaryVertex}
          (hxy : boundaryGraph.Adj x y) (hzw : boundaryGraph.Adj z w)
          (hne : ({x,y} : Finset BoundaryVertex) ≠ {z,w}) :
          Set.range (boundaryArc hxy) ∩ Set.range (boundaryArc hzw) ⊆
            {a | ∃ v : BoundaryVertex, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧ a = position v} := by
        rintro a ⟨⟨s,rfl⟩,⟨t,he⟩⟩
        by_cases hs0 : s = 0
        · subst s
          have hpos : boundaryArc hzw t = position x := by simpa only [Path.source] using he
          by_cases ht0 : t = 0
          · subst t
            have hv : z = x := hPositionInjective (by simpa only [Path.source] using hpos)
            exact ⟨x,Or.inl rfl,Or.inl hv.symm,Path.source _⟩
          by_cases ht1 : t = 1
          · subst t
            have hv : w = x := hPositionInjective (by simpa only [Path.target] using hpos)
            exact ⟨x,Or.inl rfl,Or.inr hv.symm,Path.source _⟩
          exact (hArcInteriorAvoidsVertices hzw t (hProperTime t ht0 ht1) x hpos).elim
        by_cases hs1 : s = 1
        · subst s
          have hpos : boundaryArc hzw t = position y := by simpa only [Path.target] using he
          by_cases ht0 : t = 0
          · subst t
            have hv : z = y := hPositionInjective (by simpa only [Path.source] using hpos)
            exact ⟨y,Or.inr rfl,Or.inl hv.symm,Path.target _⟩
          by_cases ht1 : t = 1
          · subst t
            have hv : w = y := hPositionInjective (by simpa only [Path.target] using hpos)
            exact ⟨y,Or.inr rfl,Or.inr hv.symm,Path.target _⟩
          exact (hArcInteriorAvoidsVertices hzw t (hProperTime t ht0 ht1) y hpos).elim
        exact (hDistinctBoundaryArcFaces hxy hzw (hBoundaryFaceDistinct hxy hzw hne)
          s (hProperTime s hs0 hs1) t he.symm).elim
      have hBoundaryArcVertex {x y : BoundaryVertex} (h : boundaryGraph.Adj x y)
          (v : BoundaryVertex) (hv : position v ∈ Set.range (boundaryArc h)) : v = x ∨ v = y := by
        obtain ⟨t,ht⟩ := hv
        by_cases ht0 : t = 0
        · subst t
          have hx : x = v := hPositionInjective (by simpa only [Path.source] using ht)
          exact Or.inl hx.symm
        by_cases ht1 : t = 1
        · subst t
          have hy : y = v := hPositionInjective (by simpa only [Path.target] using ht)
          exact Or.inr hy.symm
        exact (hArcInteriorAvoidsVertices h t (hProperTime t ht0 ht1) v ht).elim
      have hBoundaryArcRangeSymm {x y : BoundaryVertex} (h : boundaryGraph.Adj x y) :
          Set.range (boundaryArc h.symm)=Set.range (boundaryArc h) := by
        have hSub {x y : BoundaryVertex} (k : boundaryGraph.Adj x y) :
            x.val ⊆ boundaryFace k ∧ y.val ⊆ boundaryFace k := by
          have hRange := (hBoundaryArc k).2.2.1
          have h0 : boundaryArc k 0 ∈ Set.range (boundaryArc k) := ⟨0,rfl⟩
          have h1 : boundaryArc k 1 ∈ Set.range (boundaryArc k) := ⟨1,rfl⟩
          rw [hRange] at h0 h1
          exact ⟨cutMidpointFaceSubset P ⟨x.val,x.property.1⟩ _
            (by simpa only [Path.source] using h0.1),
            cutMidpointFaceSubset P ⟨y.val,y.property.1⟩ _
            (by simpa only [Path.target] using h1.1)⟩
        have hEq : boundaryFace h.symm=boundaryFace h :=
          OriginalBoundaryGeometry.actualCutFaceUnique x.val y.val _ _
            (P.card_of_mem_edges x.property.1) (P.card_of_mem_edges y.property.1)
            (fun he => h.1 (Subtype.ext he))
            (P.faces_card _ (hBoundaryArc h.symm).1) (P.faces_card _ (hBoundaryArc h).1)
            (hSub h.symm).2 (hSub h.symm).1 (hSub h).1 (hSub h).2
        rw [(hBoundaryArc h.symm).2.2.1,(hBoundaryArc h).2.2.1,hEq]
      have hActualBoundaryArcMeetReachable {x y z w : BoundaryVertex}
          (hxy : boundaryGraph.Adj x y) (hzw : boundaryGraph.Adj z w)
          (hMeet : (Set.range (boundaryArc hxy) ∩ Set.range (boundaryArc hzw)).Nonempty) :
          boundaryGraph.Reachable x z := by
        by_cases hPair : ({x,y} : Finset BoundaryVertex)={z,w}
        · have hx : x ∈ ({z,w} : Finset BoundaryVertex) := hPair ▸ (by simp)
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact .refl _
          · have hEq : x=w := Finset.mem_singleton.mp hx
            subst x
            exact hzw.symm.reachable
        · obtain ⟨a,ha,hb⟩ := hMeet
          obtain ⟨v,hvxy,hvzw,hav⟩ := hArcMeetOnlyGraphVertices hxy hzw hPair ⟨ha,hb⟩
          have hfirst : boundaryGraph.Reachable x v := by
            rcases hvxy with rfl | rfl
            · exact .refl _
            · exact hxy.reachable
          have hsecond : boundaryGraph.Reachable v z := by
            rcases hvzw with rfl | rfl
            · exact .refl _
            · exact hzw.symm.reachable
          exact hfirst.trans hsecond
      have walkPathWithin {V X : Type} [TopologicalSpace X] (G : SimpleGraph V) (position : V → X)
          (arc : ∀ {x y}, G.Adj x y → Path (position x) (position y))
          (B : Set X) (hVertex : ∀ x,position x ∈ B)
          (hArc : ∀ {x y} (h : G.Adj x y), Set.range (arc h) ⊆ B) :
          ∀ {x y}, ∀ p : G.Walk x y, ∃ f : Path (position x) (position y), Set.range f ⊆ B ∧
            ∀ v ∈ p.support, position v ∈ Set.range f := by
        intro x y p
        induction p with
        | nil =>
          refine ⟨Path.refl (position _),?_,?_⟩
          · rw [Path.refl_range]
            exact Set.singleton_subset_iff.mpr (hVertex _)
          · intro v hv
            simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hv
            subst v
            exact ⟨0,Path.source _⟩
        | @cons x z y h p ih =>
          obtain ⟨f,hf,hVerts⟩ := ih
          cases p with
          | nil =>
            refine ⟨arc h,hArc h,?_⟩
            intro v hv
            simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
              List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hv
            rcases hv with rfl | rfl
            · exact ⟨0,Path.source _⟩
            · exact ⟨1,Path.target _⟩
          | cons h' q =>
            refine ⟨(arc h).trans f,?_,?_⟩
            · rw [Path.trans_range]
              exact Set.union_subset (hArc h) hf
            · intro v hv
              have hv' : v = x ∨ v ∈ (SimpleGraph.Walk.cons h' q).support := List.mem_cons.mp hv
              rw [Path.trans_range]
              rcases hv' with rfl | hv
              · exact Or.inl ⟨0,Path.source _⟩
              · exact Or.inr (hVerts v hv)
      have hArcEmbedding {x y : BoundaryVertex} (h : boundaryGraph.Adj x y) : Topology.IsEmbedding (boundaryArc h) := (hBoundaryArc h).2.1
      let trace : ∀ {x y}, boundaryGraph.Walk x y → Set P.realization := by
        intro x y p
        induction p with
        | @nil v => exact {position v}
        | cons h p ih => exact Set.range (boundaryArc h) ∪ ih
      have hTraceNil (x : BoundaryVertex) : trace (SimpleGraph.Walk.nil : boundaryGraph.Walk x x) = {position x} := rfl
      have hTraceCons {x z y : BoundaryVertex} (h : boundaryGraph.Adj x z) (p : boundaryGraph.Walk z y) :
          trace (.cons h p) = Set.range (boundaryArc h) ∪ trace p := rfl
      have glueArcs {S : Type} [TopologicalSpace S] [T2Space S] {x y z : S}
          (f : Path x y) (g : Path y z) (hf : IsEmbedding f) (hg : IsEmbedding g)
          (hmeet : Set.range f ∩ Set.range g ⊆ {y}) :
          IsEmbedding (f.trans g) ∧
            Set.range (f.trans g) = Set.range f ∪ Set.range g := by
        have hshared (s t : unitInterval) (h : f s = g t) :
            (s : ℝ) = 1 ∧ (t : ℝ) = 0 := by
          have hfy : f s = y := Set.mem_singleton_iff.mp
            (hmeet ⟨⟨s,rfl⟩,⟨t,h.symm⟩⟩)
          have hgy : g t = y := h.symm.trans hfy
          have hs := hf.injective (hfy.trans f.target.symm)
          have ht := hg.injective (hgy.trans g.source.symm)
          exact ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
        have hinj : Function.Injective (f.trans g) := by
          intro s t he
          rw [Path.trans_apply, Path.trans_apply] at he
          by_cases hs : (s : ℝ) ≤ 1/2 <;> by_cases ht : (t : ℝ) ≤ 1/2
          · simp only [dite_eq_left hs, dite_eq_left ht] at he
            have hp := congrArg Subtype.val (hf.injective he)
            apply Subtype.ext
            change 2*(s : ℝ) = 2*(t : ℝ) at hp
            linarith
          · simp only [dite_eq_left hs, dite_eq_right ht] at he
            have hp := (hshared _ _ he).2
            change 2*(t : ℝ)-1 = 0 at hp
            have := not_le.mp ht
            linarith
          · simp only [dite_eq_right hs, dite_eq_left ht] at he
            have hp := (hshared _ _ he.symm).2
            change 2*(s : ℝ)-1 = 0 at hp
            have := not_le.mp hs
            linarith
          · simp only [dite_eq_right hs, dite_eq_right ht] at he
            have hp := congrArg Subtype.val (hg.injective he)
            apply Subtype.ext
            change 2*(s : ℝ)-1 = 2*(t : ℝ)-1 at hp
            linarith
        exact ⟨((f.trans g).continuous.isClosedEmbedding hinj).isEmbedding,
          Path.trans_range f g⟩
    
      have hFirstArcMeetTrace {x y z w : BoundaryVertex} (hxy : boundaryGraph.Adj x y) (p : boundaryGraph.Walk z w)
          (hx : x ∉ p.support) :
          Set.range (boundaryArc hxy) ∩ trace p ⊆ {position y} := by
        revert hx
        induction p with
        | @nil z =>
          intro hx a ha
          rw [hTraceNil] at ha
          have he : a = position z := Set.mem_singleton_iff.mp ha.2
          rcases hBoundaryArcVertex hxy z (he ▸ ha.1) with hz | hz
          · subst z
            exact (hx (by simp)).elim
          · exact Set.mem_singleton_iff.mpr (he.trans (congrArg position hz))
        | @cons z u w hzu p ih =>
          intro hx a ha
          have hxHead : x ≠ z := by
            intro he
            apply hx
            exact List.mem_cons.mpr (Or.inl he)
          have hxTail : x ∉ p.support := by
            intro hm
            exact hx (List.mem_cons.mpr (Or.inr hm))
          have hxNext : x ≠ u := by
            intro he
            apply hxTail
            simpa only [he] using p.start_mem_support
          rw [hTraceCons hzu p] at ha
          rcases ha.2 with hz | hz
          · have hDistinct : ({x,y} : Finset BoundaryVertex) ≠ {z,u} := by
              intro he
              have hm : x ∈ ({z,u} : Finset BoundaryVertex) := he ▸ (by simp)
              have hm' : x = z ∨ x = u := by simpa using hm
              exact hm'.elim hxHead hxNext
            obtain ⟨v,hvFirst,hvSecond,he⟩ := hArcMeetOnlyGraphVertices hxy hzu hDistinct ⟨ha.1,hz⟩
            rcases hvFirst with rfl | rfl
            · exact (hvSecond.elim hxHead hxNext).elim
            · exact Set.mem_singleton_iff.mpr he
          · exact ih hxTail ⟨ha.1,hz⟩
      have hSimpleWalkEmbedded {x y : BoundaryVertex} (p : boundaryGraph.Walk x y) :
          p.IsPath → ¬ p.Nil → ∃ f : Path (position x) (position y),
            Topology.IsEmbedding f ∧ Set.range f = trace p := by
        induction p with
        | nil =>
          intro hp hn
          exact (hn (by simp)).elim
        | @cons x z y h p ih =>
          intro hp hn
          obtain ⟨hpTail,hx⟩ := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
          cases p with
          | nil =>
            refine ⟨boundaryArc h,hArcEmbedding h,?_⟩
            rw [hTraceCons h (SimpleGraph.Walk.nil : boundaryGraph.Walk z z),hTraceNil z]
            symm
            exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr ⟨1,Path.target _⟩)
          | cons h' q =>
            obtain ⟨f,hf,hRange⟩ := ih hpTail (by simp)
            have hMeet : Set.range (boundaryArc h) ∩ Set.range f ⊆ {position z} := by
              rw [hRange]
              exact hFirstArcMeetTrace h (.cons h' q) hx
            obtain ⟨hEmb,hUnion⟩ := glueArcs (boundaryArc h) f (hArcEmbedding h) hf hMeet
            refine ⟨(boundaryArc h).trans f,hEmb,?_⟩
            rw [hUnion,hRange,hTraceCons h (.cons h' q)]
      have hArcMeetTraceEndpoints {x y z w : BoundaryVertex} (hxy : boundaryGraph.Adj x y) (p : boundaryGraph.Walk z w)
          (hNoEdge : s(x,y) ∉ p.edges) :
          Set.range (boundaryArc hxy) ∩ trace p ⊆ {position x,position y} := by
        revert hNoEdge
        induction p with
        | @nil z =>
          intro hn a ha
          rw [hTraceNil] at ha
          have he : a = position z := Set.mem_singleton_iff.mp ha.2
          rcases hBoundaryArcVertex hxy z (he ▸ ha.1) with hz | hz
          · simp [he,hz]
          · simp [he,hz]
        | @cons z u w hzu p ih =>
          intro hn a ha
          have hDifferent : s(x,y) ≠ s(z,u) := by
            intro he
            exact hn (by simp [SimpleGraph.Walk.edges_cons,he])
          have hTail : s(x,y) ∉ p.edges := by
            intro hm
            exact hn (by simp [SimpleGraph.Walk.edges_cons,hm])
          have hPair : ({x,y} : Finset BoundaryVertex) ≠ {z,u} := by
            intro he
            have hx : x = z ∨ x = u := by
              have hm : x ∈ ({z,u} : Finset BoundaryVertex) := he ▸ (by simp)
              simpa using hm
            have hy : y = z ∨ y = u := by
              have hm : y ∈ ({z,u} : Finset BoundaryVertex) := he ▸ (by simp)
              simpa using hm
            apply hDifferent
            apply Sym2.eq_iff.mpr
            rcases hx with hx | hx <;> rcases hy with hy | hy
            · exact (hxy.ne (hx.trans hy.symm)).elim
            · exact Or.inl ⟨hx,hy⟩
            · exact Or.inr ⟨hx,hy⟩
            · exact (hxy.ne (hx.trans hy.symm)).elim
          rw [hTraceCons hzu p] at ha
          rcases ha.2 with hm | hm
          · obtain ⟨v,hv,_,he⟩ := hArcMeetOnlyGraphVertices hxy hzu hPair ⟨ha.1,hm⟩
            rcases hv with rfl | rfl <;> simp [he]
          · exact ih hTail ⟨ha.1,hm⟩
      have hCycleTwoArcs {x : BoundaryVertex} (p : boundaryGraph.Walk x x) (hp : p.IsCycle) :
          ∃ y : BoundaryVertex, ∃ f : Path (position x) (position y), ∃ g : Path (position y) (position x),
            Topology.IsEmbedding f ∧ Topology.IsEmbedding g ∧
            Set.range f ∩ Set.range g ⊆ {position x,position y} ∧
            Set.range f ∪ Set.range g = trace p := by
        cases p with
        | nil => exact (hp.not_nil (by simp)).elim
        | @cons x y z h q =>
          have hPath : q.IsPath := by simpa using hp.isPath_tail
          have hNotNil : ¬ q.Nil := by
            intro hn
            have hl := hp.three_le_length
            have hq : q.length = 0 := (SimpleGraph.Walk.length_eq_zero_iff).mpr hn
            simp only [SimpleGraph.Walk.length_cons,hq] at hl
            omega
          obtain ⟨g,hg,hRange⟩ := hSimpleWalkEmbedded q hPath hNotNil
          have hNoEdge : s(x,y) ∉ q.edges := (SimpleGraph.Walk.isTrail_cons h q).mp hp.isTrail |>.2
          refine ⟨y,boundaryArc h,g,hArcEmbedding h,hg,?_,?_⟩
          · rw [hRange]
            exact hArcMeetTraceEndpoints h q hNoEdge
          · rw [hRange,hTraceCons h q]
      have hCycleCurve {x : BoundaryVertex} (p : boundaryGraph.Walk x x) (hp : p.IsCycle) :
          ∃ c : CurveComplex.Curve P.realization, ∃ y : BoundaryVertex,
            ∃ f : Path (position x) (position y), ∃ g : Path (position y) (position x),
              c.image = Set.range f ∪ Set.range g ∧ c.image = trace p := by
        obtain ⟨y,f,g,hf,hg,hMeet,hTrace⟩ := hCycleTwoArcs p hp
        let g' := g.symm
        have hg' : Topology.IsEmbedding g' := hg.comp (unitInterval.symmHomeomorph.isEmbedding)
        have hMeet' : Set.range f ∩ Set.range g' ⊆ {position x,position y} := by
          rw [Path.symm_range]
          exact hMeet
        have hCollision : ∀ s t : unitInterval, f s = g' t →
            (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
          intro s t he
          have ha := hMeet' ⟨Set.mem_range_self s,⟨t,he.symm⟩⟩
          rcases ha with ha | ha
          · exact Or.inl ⟨hf.injective (ha.trans f.source.symm),
              hg'.injective (he.symm.trans (ha.trans g'.source.symm))⟩
          · exact Or.inr ⟨hf.injective (ha.trans f.target.symm),
              hg'.injective (he.symm.trans (ha.trans g'.target.symm))⟩
        obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f.toContinuousMap g'.toContinuousMap hf.injective hg'.injective
          (f.source.trans g'.source.symm) (f.target.trans g'.target.symm) hCollision
        have hc' : c.image = Set.range f ∪ Set.range g := by
          change c.image = Set.range f ∪ Set.range g.symm at hc
          simpa only [Path.symm_range] using hc
        exact ⟨c,y,f,g,hc',hc'.trans hTrace⟩
      have nullBoundaryTransport {R U : Type} [TopologicalSpace R] [T2Space R]
          [TopologicalSpace U] [T2Space U] [SimplyConnectedSpace U]
          (m : R → U) (hm : Topology.IsEmbedding m) {x y : R}
          (f0 : Path x y) (g0 : Path y x)
          (hf0 : Topology.IsEmbedding f0) (hg0 : Topology.IsEmbedding g0)
          (hMeet : Set.range f0 ∩ Set.range g0 ⊆ {x,y}) :
          ∃ c : CurveComplex.Curve U, c.image = m '' (Set.range f0 ∪ Set.range g0) ∧
            (⟨c.map,c.embedded.continuous⟩ : C(Circle,U)).Nullhomotopic := by
        let f := f0.map hm.continuous
        let g := g0.symm.map hm.continuous
        have hf : Topology.IsEmbedding f := hm.comp hf0
        have hg : Topology.IsEmbedding g := hm.comp
          (hg0.comp unitInterval.symmHomeomorph.isEmbedding)
        have hmeet : ∀ s t, f s = g t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
          intro s t he
          have he0 : f0 s = g0.symm t := hm.injective he
          have ha : f0 s ∈ ({x,y} : Set R) := hMeet
            ⟨Set.mem_range_self s,⟨unitInterval.symm t,he0.symm⟩⟩
          rcases ha with ha | ha
          · exact Or.inl ⟨hf.injective (congrArg m ha |>.trans f.source.symm),
              hg.injective (he.symm.trans ((congrArg m ha).trans g.source.symm))⟩
          · exact Or.inr ⟨hf.injective (congrArg m ha |>.trans f.target.symm),
              hg.injective (he.symm.trans ((congrArg m ha).trans g.target.symm))⟩
        have hnull : (f.trans g.symm).Homotopic (Path.refl (m x)) :=
          SimplyConnectedSpace.paths_homotopic _ _
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
        obtain ⟨c,hc,hcn⟩ := CurveComplex.LocalSurgery.nullhomotopic_loop_with_only_endpoint_collision_gives_curve
          (m x) (f.trans g.symm) hloopCollision hnull
        refine ⟨c,hc.trans ?_,hcn⟩
        rw [Path.trans_range,Path.symm_range]
        change Set.range (m ∘ f0) ∪ Set.range (m ∘ g0.symm) = m '' (Set.range f0 ∪ Set.range g0)
        rw [Set.range_comp,Set.range_comp,Path.symm_range,Set.image_union]
      let halfLevel : Set P.realization := {x | (∑ v ∈ selected,x.val v) = (1 : ℝ)/2}
      have hPositionHalf (v : BoundaryVertex) : position v ∈ halfLevel := by
        obtain ⟨w,hw⟩ := hBoundaryGraph.2 v
        have hRange := (hBoundaryArc hw).2.2.1
        have hAt : boundaryArc hw 0 ∈ Set.range (boundaryArc hw) := ⟨0,rfl⟩
        rw [hRange] at hAt
        simpa only [halfLevel,Set.mem_setOf_eq,Path.source] using hAt.2
      have hArcHalf {x y : BoundaryVertex} (h : boundaryGraph.Adj x y) :
          Set.range (boundaryArc h) ⊆ halfLevel := by
        intro z hz
        rw [(hBoundaryArc h).2.2.1] at hz
        exact hz.2
      have hTraceHalf {x y : BoundaryVertex} (p : boundaryGraph.Walk x y) : trace p ⊆ halfLevel := by
        induction p with
        | @nil v =>
          rw [hTraceNil]
          exact Set.singleton_subset_iff.mpr (hPositionHalf v)
        | cons h p ih =>
          rw [hTraceCons h p]
          exact Set.union_subset (hArcHalf h) ih
      have hActualSimpleBoundaryPath {x y : BoundaryVertex} (p : boundaryGraph.Walk x y)
          (hp : p.IsPath) (hn : ¬ p.Nil) :
          ∃ f : Path (position x) (position y), Topology.IsEmbedding f ∧
            Set.range f = trace p ∧ Set.range (realizationMap ∘ f) ⊆ frontier N ∧
            Set.range (realizationMap ∘ f) ⊆ Kᶜ := by
        obtain ⟨f,hf,hRange⟩ := hSimpleWalkEmbedded p hp hn
        refine ⟨f,hf,hRange,?_,?_⟩
        · rintro z ⟨t,rfl⟩
          exact hActualHalfFrontier (f t) (hTraceHalf p (hRange ▸ Set.mem_range_self t))
        · rintro z ⟨t,rfl⟩ hzK
          exact (hActualHalfFrontier (f t) (hTraceHalf p (hRange ▸ Set.mem_range_self t))).2 (hOriginalK hzK)
      have hActualBoundaryCyclePath (v : BoundaryVertex) :
          ∃ p : boundaryGraph.Walk v v, p.IsCycle ∧
            p.toSubgraph.verts = (boundaryGraph.connectedComponentMk v).supp ∧
            ∃ q : Path (position v) (position v),
              Set.range q ⊆ halfLevel ∧
              (∀ w ∈ p.support, position w ∈ Set.range q) ∧
              Set.range (realizationMap ∘ q) ⊆ frontier N ∧
              Set.range (realizationMap ∘ q) ⊆ Kᶜ := by
        obtain ⟨p,hp,hComponent⟩ := hBoundaryCycles v
        obtain ⟨q,hq,hVertices⟩ := walkPathWithin boundaryGraph position
          (fun {_ _} h => boundaryArc h) halfLevel hPositionHalf (fun {_ _} h => hArcHalf h) p
        refine ⟨p,hp,hComponent,q,hq,hVertices,?_,?_⟩
        · rintro z ⟨t,rfl⟩
          exact hActualHalfFrontier (q t) (hq ⟨t,rfl⟩)
        · rintro z ⟨t,rfl⟩ hzK
          exact (hActualHalfFrontier (q t) (hq ⟨t,rfl⟩)).2 (hOriginalK hzK)
      have hActualEmbeddedBoundaryCycle (v : BoundaryVertex) :
          ∃ p : boundaryGraph.Walk v v, p.IsCycle ∧
            p.toSubgraph.verts = (boundaryGraph.connectedComponentMk v).supp ∧
            ∃ c : CurveComplex.Curve P.realization, c.image = trace p ∧
              realizationMap '' c.image ⊆ frontier N ∧
              realizationMap '' c.image ⊆ Kᶜ := by
        obtain ⟨p,hp,hComponent⟩ := hBoundaryCycles v
        obtain ⟨c,y,f,g,hUnion,hTrace⟩ := hCycleCurve p hp
        refine ⟨p,hp,hComponent,c,hTrace,?_,?_⟩
        · rintro z ⟨a,ha,rfl⟩
          exact hActualHalfFrontier a (hTraceHalf p (hTrace ▸ ha))
        · rintro z ⟨a,ha,rfl⟩ hzK
          exact (hActualHalfFrontier a (hTraceHalf p (hTrace ▸ ha))).2 (hOriginalK hzK)
      have hActualNullBoundaryCycle (v : BoundaryVertex) :
          ∃ p : boundaryGraph.Walk v v, p.IsCycle ∧
            p.toSubgraph.verts = (boundaryGraph.connectedComponentMk v).supp ∧
            ∃ c : CurveComplex.Curve U, c.image = realizationMap '' trace p ∧
              (⟨c.map,c.embedded.continuous⟩ : C(Circle,U)).Nullhomotopic ∧
              c.image ⊆ frontier N ∧ c.image ⊆ Kᶜ := by
        obtain ⟨p,hp,hComponent⟩ := hBoundaryCycles v
        obtain ⟨y,f,g,hf,hg,hMeet,hTrace⟩ := hCycleTwoArcs p hp
        obtain ⟨c,hImage,hNull⟩ := nullBoundaryTransport realizationMap hRealizationEmbedding f g hf hg hMeet
        have hc : c.image = realizationMap '' trace p := by rw [hImage,hTrace]
        refine ⟨p,hp,hComponent,c,hc,hNull,?_,?_⟩
        · rw [hc]
          rintro z ⟨a,ha,rfl⟩
          exact hActualHalfFrontier a (hTraceHalf p ha)
        · rw [hc]
          rintro z ⟨a,ha,rfl⟩ hzK
          exact (hActualHalfFrontier a (hTraceHalf p ha)).2 (hOriginalK hzK)
      have twoEdgesDetermineFace {V : Type} [DecidableEq V] (e d face face' : Finset V)
          (he : e.card = 2) (hd : d.card = 2) (hne : e ≠ d)
          (hf : face.card = 3) (hf' : face'.card = 3)
          (hef : e ⊆ face) (hdf : d ⊆ face)
          (hef' : e ⊆ face') (hdf' : d ⊆ face') : face = face' := by
        have hNot : ¬ d ⊆ e := by
          intro h
          exact hne (Finset.eq_of_subset_of_card_le h (by omega)).symm
        have hUnionNe : e ≠ e ∪ d := by
          intro h
          apply hNot
          rw [h]
          exact Finset.subset_union_right
        have hStrict : e ⊂ e ∪ d := Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_union_left,hUnionNe⟩
        have hLower := Finset.card_lt_card hStrict
        have hUpper := Finset.card_le_card (Finset.union_subset hef hdf)
        have hCard : (e ∪ d).card = 3 := by omega
        have hFirst : e ∪ d = face := Finset.eq_of_subset_of_card_le
          (Finset.union_subset hef hdf) (by omega)
        have hSecond : e ∪ d = face' := Finset.eq_of_subset_of_card_le
          (Finset.union_subset hef' hdf') (by omega)
        exact hFirst.symm.trans hSecond
      have hHalfLevelOnGraphArc (x : P.realization)
          (hHalf : (∑ v ∈ selected,x.val v) = (1 : ℝ)/2) :
          ∃ u v : BoundaryVertex, ∃ h : boundaryGraph.Adj u v,
            x ∈ Set.range (boundaryArc h) := by
        obtain ⟨face,hFace,hCarrier⟩ := x.property.2
        obtain ⟨hYes,hNo⟩ := halfLevelMixed P selected face x hCarrier hHalf
        obtain ⟨f,hf,hRange,u,v,hu,hv,hAdj,hInterior⟩ := hActualMatchedTriangleArc face hFace hYes hNo
        have huFace : u.val ⊆ face := by
          apply cutMidpointFaceSubset P ⟨u.val,u.property.1⟩ face
          have ha : f 0 ∈ Set.range f := ⟨0,rfl⟩
          rw [hRange] at ha
          exact hu ▸ ha.1
        have hvFace : v.val ⊆ face := by
          apply cutMidpointFaceSubset P ⟨v.val,v.property.1⟩ face
          have ha : f 1 ∈ Set.range f := ⟨1,rfl⟩
          rw [hRange] at ha
          exact hv ▸ ha.1
        have huChosen : u.val ⊆ boundaryFace hAdj := by
          apply cutMidpointFaceSubset P ⟨u.val,u.property.1⟩ (boundaryFace hAdj)
          have ha : boundaryArc hAdj 0 ∈ Set.range (boundaryArc hAdj) := ⟨0,rfl⟩
          rw [(hBoundaryArc hAdj).2.2.1] at ha
          simpa only [Path.source] using ha.1
        have hvChosen : v.val ⊆ boundaryFace hAdj := by
          apply cutMidpointFaceSubset P ⟨v.val,v.property.1⟩ (boundaryFace hAdj)
          have ha : boundaryArc hAdj 1 ∈ Set.range (boundaryArc hAdj) := ⟨1,rfl⟩
          rw [(hBoundaryArc hAdj).2.2.1] at ha
          simpa only [Path.target] using ha.1
        have hEqual : face = boundaryFace hAdj := twoEdgesDetermineFace u.val v.val face (boundaryFace hAdj)
          (P.card_of_mem_edges u.property.1) (P.card_of_mem_edges v.property.1)
          (fun he => hAdj.1 (Subtype.ext he)) (P.faces_card face hFace)
          (P.faces_card _ (hBoundaryArc hAdj).1) huFace hvFace huChosen hvChosen
        refine ⟨u,v,hAdj,?_⟩
        rw [(hBoundaryArc hAdj).2.2.1,← hEqual]
        exact ⟨hCarrier,hHalf⟩
      have hEveryFrontierPointOnNullCurve (z : U) (hz : z ∈ frontier N) :
          ∃ c : CurveComplex.Curve U, z ∈ c.image ∧
            (⟨c.map,c.embedded.continuous⟩ : C(Circle,U)).Nullhomotopic ∧
            c.image ⊆ frontier N ∧ c.image ⊆ Kᶜ := by
        have hzN : z ∈ N := hNCompact.isClosed.closure_eq ▸ frontier_subset_closure hz
        rw [hRefinedImage] at hzN
        obtain ⟨a,ha,haz⟩ := hzN
        have hFront : realizationMap a ∈ frontier N := haz.symm ▸ hz
        obtain ⟨u,v,hAdj,hOnArc⟩ := hHalfLevelOnGraphArc a (hFrontierLevel a hFront)
        obtain ⟨p,hp,hComponent⟩ := hBoundaryCycles u
        have hNeighbors : p.toSubgraph.neighborSet u = boundaryGraph.neighborSet u := by
          apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset u)
          rw [hBoundaryGraph.1 (hBoundaryGraph.2 u),hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support]
        have hSubAdj : p.toSubgraph.Adj u v := by
          change v ∈ p.toSubgraph.neighborSet u
          rw [hNeighbors]
          exact hAdj
        obtain ⟨q,hq,hSnd,hVerts⟩ := hp.exists_isCycle_snd_verts_eq hSubAdj
        have hArcSubset : Set.range (boundaryArc hAdj) ⊆ trace q := by
          cases q with
          | nil => exact (hq.not_nil (by simp)).elim
          | @cons x y w hh r =>
            have hy : y = v := by simpa only [SimpleGraph.Walk.snd_cons] using hSnd
            subst y
            rw [hTraceCons hh r]
            exact Set.subset_union_left
        obtain ⟨w,f,g,hf,hg,hMeet,hTrace⟩ := hCycleTwoArcs q hq
        obtain ⟨c,hImage,hNull⟩ := nullBoundaryTransport realizationMap hRealizationEmbedding f g hf hg hMeet
        have hc : c.image = realizationMap '' trace q := by rw [hImage,hTrace]
        refine ⟨c,?_,hNull,?_,?_⟩
        · rw [hc]
          exact ⟨a,hArcSubset hOnArc,haz⟩
        · rw [hc]
          rintro z ⟨a,ha,rfl⟩
          exact hActualHalfFrontier a (hTraceHalf q ha)
        · rw [hc]
          rintro z ⟨a,ha,rfl⟩ hzK
          exact (hActualHalfFrontier a (hTraceHalf q ha)).2 (hOriginalK hzK)
      have hActualNullCurveCoveringBoundaryEdge (u v : BoundaryVertex)
          (hAdj : boundaryGraph.Adj u v) :
          ∃ c : CurveComplex.Curve U,
            realizationMap '' Set.range (boundaryArc hAdj) ⊆ c.image ∧
            (⟨c.map,c.embedded.continuous⟩ : C(Circle,U)).Nullhomotopic ∧
            c.image ⊆ frontier N ∧ c.image ⊆ Kᶜ := by
        obtain ⟨p,hp,hComponent⟩ := hBoundaryCycles u
        have hNeighbors : p.toSubgraph.neighborSet u = boundaryGraph.neighborSet u := by
          apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset u)
          rw [hBoundaryGraph.1 (hBoundaryGraph.2 u),hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support]
        have hSubAdj : p.toSubgraph.Adj u v := by
          change v ∈ p.toSubgraph.neighborSet u
          rw [hNeighbors]
          exact hAdj
        obtain ⟨q,hq,hSnd,hVerts⟩ := hp.exists_isCycle_snd_verts_eq hSubAdj
        have hArcSubset : Set.range (boundaryArc hAdj) ⊆ trace q := by
          cases q with
          | nil => exact (hq.not_nil (by simp)).elim
          | @cons x y w hh r =>
            have hy : y = v := by simpa only [SimpleGraph.Walk.snd_cons] using hSnd
            subst y
            rw [hTraceCons hh r]
            exact Set.subset_union_left
        obtain ⟨w,f,g,hf,hg,hMeet,hTrace⟩ := hCycleTwoArcs q hq
        obtain ⟨c,hImage,hNull⟩ := nullBoundaryTransport realizationMap hRealizationEmbedding f g hf hg hMeet
        have hc : c.image = realizationMap '' trace q := by rw [hImage,hTrace]
        refine ⟨c,?_,hNull,?_,?_⟩
        · rw [hc]
          rintro z ⟨a,ha,rfl⟩
          exact ⟨a,hArcSubset ha,rfl⟩
        · rw [hc]
          rintro z ⟨a,ha,rfl⟩
          exact hActualHalfFrontier a (hTraceHalf q ha)
        · rw [hc]
          rintro z ⟨a,ha,rfl⟩ hzK
          exact (hActualHalfFrontier a (hTraceHalf q ha)).2 (hOriginalK hzK)
      have hActualIsolatedNullCurveCoveringBoundaryEdge (u v : BoundaryVertex)
          (hAdj : boundaryGraph.Adj u v) :
          ∃ c : CurveComplex.Curve U,
            realizationMap '' Set.range (boundaryArc hAdj) ⊆ c.image ∧
            (⟨c.map,c.embedded.continuous⟩ : C(Circle,U)).Nullhomotopic ∧
            c.image ⊆ frontier N ∧ c.image ⊆ Kᶜ ∧
            ∃ V : Set U, IsOpen V ∧ c.image ⊆ V ∧
              ∀ z ∈ V, z ∈ frontier N ↔ z ∈ c.image := by
        obtain ⟨p,hp,hComponent⟩ := hBoundaryCycles u
        have hDegree : ∀ x, (boundaryGraph.neighborSet x).ncard=2 :=
          fun x => hBoundaryGraph.1 (hBoundaryGraph.2 x)
        have hCoverEdge {x y : BoundaryVertex} (h : boundaryGraph.Adj x y)
            (hx : boundaryGraph.Reachable u x) : Set.range (boundaryArc h) ⊆ trace p :=
          OriginalBoundaryGeometry.actualCycleTraceCoversComponentEdges
            boundaryGraph position boundaryArc trace hTraceCons hBoundaryArcRangeSymm
            hDegree p hp hComponent h hx
        obtain ⟨w,f,g,hf,hg,hMeet,hTrace⟩ := hCycleTwoArcs p hp
        obtain ⟨c,hImage,hNull⟩ := nullBoundaryTransport realizationMap hRealizationEmbedding f g hf hg hMeet
        have hc : c.image=realizationMap '' trace p := by rw [hImage,hTrace]
        let OtherEdge := {i : BoundaryVertex × BoundaryVertex //
          boundaryGraph.Adj i.1 i.2 ∧ ¬ boundaryGraph.Reachable u i.1}
        let O : Set U := ⋃ i : OtherEdge, Set.range (fun t : unitInterval =>
          realizationMap (boundaryArc i.property.1 t))
        have hO : IsCompact O := isCompact_iUnion (fun i => isCompact_range
          (hRealizationEmbedding.continuous.comp (boundaryArc i.property.1).continuous))
        have hDisj : c.image ⊆ Oᶜ := by
          rw [hc]
          rintro z ⟨a,ha,rfl⟩ hz
          obtain ⟨i,t,ht⟩ := Set.mem_iUnion.mp hz
          have hta : boundaryArc i.property.1 t=a := hRealizationEmbedding.injective ht
          have hReach := OriginalBoundaryGeometry.actualWalkTraceArcComponent
            boundaryGraph position hPositionInjective boundaryArc trace hTraceNil hTraceCons
            hBoundaryArcVertex hActualBoundaryArcMeetReachable p i.property.1
            ⟨a,ha,⟨t,hta⟩⟩
          exact i.property.2 hReach
        have hcFront : c.image ⊆ frontier N := by
          rw [hc]
          rintro z ⟨a,ha,rfl⟩
          exact hActualHalfFrontier a (hTraceHalf p ha)
        refine ⟨c,?_,hNull,hcFront,?_,Oᶜ,hO.isClosed.isOpen_compl,hDisj,?_⟩
        · rw [hc]
          exact Set.image_mono (hCoverEdge hAdj (.refl _))
        · intro z hz hzK
          exact (hcFront hz).2 (hOriginalK hzK)
        · intro z hz
          constructor
          · intro hFront
            have hzN : z ∈ N := hNCompact.isClosed.closure_eq ▸ frontier_subset_closure hFront
            rw [hRefinedImage] at hzN
            obtain ⟨a,ha,haz⟩ := hzN
            have hHalf : (∑ x ∈ selected,a.val x)=(1 : ℝ)/2 :=
              hFrontierLevel a (haz.symm ▸ hFront)
            obtain ⟨x,y,hxy,hOn⟩ := hHalfLevelOnGraphArc a hHalf
            have hReach : boundaryGraph.Reachable u x := by
              by_contra hNot
              apply hz
              let i : OtherEdge := ⟨(x,y),hxy,hNot⟩
              apply Set.mem_iUnion.mpr
              refine ⟨i,?_⟩
              obtain ⟨t,ht⟩ := hOn
              exact ⟨t,(congrArg realizationMap ht).trans haz⟩
            rw [hc]
            exact ⟨a,hCoverEdge hxy hReach hOn,haz⟩
          · intro hzc
            exact hcFront hzc
      have hActualCompactBoundaryHomotopyHull :
          ∃ J : Set U, IsCompact J ∧ N ⊆ J ∧
            ∀ z ∈ frontier N, ∃ c : CurveComplex.Curve U,
              z ∈ c.image ∧ c.image ⊆ frontier N ∧ c.image ⊆ Kᶜ ∧
              ∃ y : U, ∃ H : ContinuousMap.Homotopy
                (⟨c.map,c.embedded.continuous⟩ : C(Circle,U))
                (ContinuousMap.const Circle y), Set.range H ⊆ J ∧ ∃ V : Set U, IsOpen V ∧ c.image ⊆ V ∧
                  ∀ z ∈ V, z ∈ frontier N ↔ z ∈ c.image := by
        let EdgeIndex := {uv : BoundaryVertex × BoundaryVertex // boundaryGraph.Adj uv.1 uv.2}
        have hForIndex : ∀ i : EdgeIndex, ∃ c : CurveComplex.Curve U,
            realizationMap '' Set.range (boundaryArc i.property) ⊆ c.image ∧
            (⟨c.map,c.embedded.continuous⟩ : C(Circle,U)).Nullhomotopic ∧
            c.image ⊆ frontier N ∧ c.image ⊆ Kᶜ ∧
            ∃ V : Set U, IsOpen V ∧ c.image ⊆ V ∧
              ∀ z ∈ V, z ∈ frontier N ↔ z ∈ c.image := fun i =>
          hActualIsolatedNullCurveCoveringBoundaryEdge i.val.1 i.val.2 i.property
        choose c hArcCover hNull hFrontier hAvoid V hV hCV hFIff using hForIndex
        have hChoice : ∀ i, ∃ y : U, Nonempty (ContinuousMap.Homotopy
            (⟨(c i).map,(c i).embedded.continuous⟩ : C(Circle,U))
            (ContinuousMap.const Circle y)) := hNull
        choose y hH using hChoice
        let H (i : EdgeIndex) := (hH i).some
        let J : Set U := N ∪ ⋃ i, Set.range (H i)
        have hJ : IsCompact J := hNCompact.union
          (isCompact_iUnion fun i => isCompact_range (H i).continuous)
        refine ⟨J,hJ,Set.subset_union_left,?_⟩
        intro z hz
        have hzN : z ∈ N := hNCompact.isClosed.closure_eq ▸ frontier_subset_closure hz
        rw [hRefinedImage] at hzN
        obtain ⟨a,ha,haz⟩ := hzN
        have hFront : realizationMap a ∈ frontier N := haz.symm ▸ hz
        obtain ⟨u,v,hAdj,hOnArc⟩ := hHalfLevelOnGraphArc a (hFrontierLevel a hFront)
        let i : EdgeIndex := ⟨(u,v),hAdj⟩
        refine ⟨c i,hArcCover i ⟨a,hOnArc,haz⟩,hFrontier i,hAvoid i,y i,H i,?_,V i,hV i,hCV i,hFIff i⟩
        intro x hx
        exact Or.inr (Set.mem_iUnion.mpr ⟨i,hx⟩)
      have hActualBoundaryVertexNonempty (hKNonempty : K.Nonempty) : Nonempty BoundaryVertex := by
        have hNNonempty : N.Nonempty := hKNonempty.mono (hOriginalK.trans interior_subset)
        have hNNeUniv : N ≠ Set.univ := by
          intro he
          apply hCompact
          simpa only [he] using hNCompact
        obtain ⟨y,hy⟩ := nonempty_frontier_iff.mpr ⟨hNNonempty,hNNeUniv⟩
        have hyN : y ∈ N := hNCompact.isClosed.closure_eq ▸ frontier_subset_closure hy
        rw [hRefinedImage] at hyN
        obtain ⟨x,hx,hxy⟩ := hyN
        have hxFront : realizationMap x ∈ frontier N := hxy.symm ▸ hy
        obtain ⟨face,hFace,hOutside⟩ := x.property.2
        have hCarrier : x ∈ P.faceCarrier face := hOutside
        have hHalf := hFrontierLevel x hxFront
        obtain ⟨hYes,hNo⟩ := halfLevelMixed P selected face x hCarrier hHalf
        obtain ⟨f,hf,hRange,u,v,hu,hv,hAdj,hInterior⟩ := hActualMatchedTriangleArc face hFace hYes hNo
        exact ⟨u⟩
      have actualLocalChartDisk {U : Type} [TopologicalSpace U] [Nonempty U]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U] :
          ∃ D : Set U, IsCompact D ∧
            Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ D) := by
        let x : U := Classical.choice inferInstance
        let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
        obtain ⟨r,hr,hBall,hIn,hCompact,hConnected,hOpen,hx⟩ :=
          CurveComplex.exists_compact_chart_disk_in_open x Set.univ isOpen_univ (Set.mem_univ _)
        let normal : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
          (Homeomorph.smulOfNeZero (α := EuclideanSpace ℝ (Fin 2)) r (ne_of_gt hr)).trans
            (Homeomorph.addLeft (e x))
        have hNormal : ∀ z, z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
            normal z ∈ Metric.closedBall (e x) r := by
          intro z
          rw [Metric.mem_closedBall,Metric.mem_closedBall,dist_zero_right]
          change ‖z‖ ≤ 1 ↔ dist (e x + r • z) (e x) ≤ r
          rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
          constructor <;> intro hz <;> nlinarith
        let hNorm := normal.subtype hNormal
        let D := e.symm '' Metric.closedBall (e x) r
        have hChart : Nonempty (Metric.closedBall (e x) r ≃ₜ D) :=
          ⟨e.symm.homeomorphOfImageSubsetSource hBall rfl⟩
        exact ⟨D,hCompact,⟨hNorm.trans hChart.some⟩⟩
      have actualConnectedComponent {U : Type} [TopologicalSpace U] [T2Space U] [LocallyConnectedSpace U]
          (K L N : Set U) (hKL : K ⊆ L) (hL : IsConnected L)
          (hLN : L ⊆ interior N) (hN : IsCompact N) :
          ∃ C : Set U, IsCompact C ∧ IsConnected C ∧ K ⊆ interior C ∧
            C ⊆ N ∧ frontier C ⊆ frontier N ∧
            ∃ base ∈ L, C = connectedComponentIn N base := by
        classical
        obtain ⟨base,hBase⟩ := hL.1
        have hBaseN : base ∈ N := interior_subset (hLN hBase)
        let C := connectedComponentIn N base
        have hLC : L ⊆ C := hL.2.subset_connectedComponentIn hBase (hLN.trans interior_subset)
        letI : CompactSpace N := isCompact_iff_compactSpace.mp hN
        have hCCompact : IsCompact C := by
          dsimp [C]
          rw [connectedComponentIn_eq_image hBaseN]
          exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
        have hCInterior {x : U} (hx : x ∈ C) (hxN : x ∈ interior N) : x ∈ interior C := by
          apply mem_interior_iff_mem_nhds.mpr
          change connectedComponentIn N base ∈ nhds x
          rw [connectedComponentIn_eq hx]
          exact connectedComponentIn_mem_nhds (mem_interior_iff_mem_nhds.mp hxN)
        refine ⟨C,hCCompact,isConnected_connectedComponentIn_iff.mpr hBaseN,?_,
          connectedComponentIn_subset N base,?_,?_⟩
        · intro x hx
          exact hCInterior (hLC (hKL hx)) (hLN (hKL hx))
        · intro x hx
          have hxC : x ∈ C := hCCompact.isClosed.closure_eq ▸ frontier_subset_closure hx
          refine ⟨subset_closure (connectedComponentIn_subset N base hxC),?_⟩
          intro hxN
          exact hx.2 (hCInterior hxC hxN)
        · exact ⟨base,hBase,rfl⟩
      obtain ⟨connectedN,hConnectedNCompact,hConnectedNConnected,hKConnectedNInterior,
        hConnectedNSubset,hConnectedNFrontier,base,hBaseHull,hConnectedNComponent⟩ :=
        actualConnectedComponent K originalHull N hKHull hHullConnected hHullInterior hNCompact
      letI : LocallyPathConnectedSpace N :=
        ChartedSpace.locallyPathConnectedSpace (EuclideanHalfSpace 2) N
      have hBaseN : base ∈ N := interior_subset (hHullInterior hBaseHull)
      let componentOpen : TopologicalSpace.Opens N :=
        ⟨connectedComponent (⟨base,hBaseN⟩ : N),isOpen_connectedComponent⟩
      have hComponentImage : Subtype.val '' (componentOpen : Set N) = connectedN := by
        change Subtype.val '' connectedComponent (⟨base,hBaseN⟩ : N) = connectedN
        rw [hConnectedNComponent,connectedComponentIn_eq_image hBaseN]
      let actualComponentHomeomorph : componentOpen ≃ₜ connectedN :=
        (Topology.IsEmbedding.subtypeVal.homeomorphImage (componentOpen : Set N)).trans
          (Homeomorph.setCongr hComponentImage)
      letI : ChartedSpace (EuclideanHalfSpace 2) connectedN :=
        actualComponentHomeomorph.chartedSpace
      letI : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 connectedN := inferInstance
      letI : CompactSpace connectedN := isCompact_iff_compactSpace.mp hConnectedNCompact
      letI : ConnectedSpace connectedN := Subtype.connectedSpace hConnectedNConnected
      have hConnectedNInteriorRegular : IsConnected (interior connectedN) ∧
          closure (interior connectedN)=connectedN := by
        let rawBase : B := actualHalfHomeomorph.symm ⟨base,hBaseN⟩
        have hComponentIff (x : B) : x ∈ connectedComponent rawBase ↔
            actualHalfHomeomorph x ∈ connectedComponent (⟨base,hBaseN⟩ : N) := by
          constructor
          · intro hx
            have h := actualHalfHomeomorph.continuous.image_connectedComponent_subset
              rawBase ⟨x,hx,rfl⟩
            simpa only [rawBase,actualHalfHomeomorph.apply_symm_apply] using h
          · intro hx
            have h := actualHalfHomeomorph.symm.continuous.image_connectedComponent_subset
              (⟨base,hBaseN⟩ : N) ⟨actualHalfHomeomorph x,hx,rfl⟩
            simpa only [actualHalfHomeomorph.symm_apply_apply] using h
        let W : Set B := {x | x ∈ connectedComponent rawBase ∧
          (1 : ℝ)/2 < ∑ v ∈ selected,x.val.val v}
        have hW : IsConnected W := OriginalHalfLevelInterior.actualStrictComponentConnected P selected rawBase
        have hEq : (fun x : B => realizationMap x.val) '' W = interior connectedN := by
          ext y
          constructor
          · rintro ⟨x,hx,rfl⟩
            have hCy : realizationMap x.val ∈ connectedN := by
              rw [←hComponentImage]
              exact ⟨actualHalfHomeomorph x,hComponentIff x |>.mp hx.1,rfl⟩
            have hStrictOpen : IsOpen {z : P.realization | (1 : ℝ)/2 < ∑ v ∈ selected,z.val v} := by
              apply isOpen_lt continuous_const
              fun_prop
            have hStrictInt : x.val ∈ interior B :=
              hStrictOpen.subset_interior_iff.mpr
                (show {z : P.realization | (1 : ℝ)/2 < ∑ v ∈ selected,z.val v} ⊆ B from
                  fun z hz => (show (1 : ℝ)/2 < ∑ v ∈ selected,z.val v from hz).le) hx.2
            have hNInterior : realizationMap x.val ∈ interior N := by
              have hRI : R.homeo x.val ∈ interior A := by
                have hAeq : A = R.homeo '' B := by
                  ext z
                  constructor
                  · intro hz
                    exact ⟨R.homeo.symm z,hz,R.homeo.apply_symm_apply z⟩
                  · rintro ⟨w,hw,rfl⟩
                    change (1 : ℝ)/2 ≤ ∑ v ∈ selected,w.val v at hw
                    change (1 : ℝ)/2 ≤ ∑ v ∈ selected,(R.homeo.symm (R.homeo w)).val v
                    simpa only [R.homeo.symm_apply_apply] using hw
                rw [hAeq,←R.homeo.image_interior]
                exact ⟨x.val,hStrictInt,rfl⟩
              exact hImageInterior ⟨R.homeo x.val,hRI,rfl⟩
            apply mem_interior_iff_mem_nhds.mpr
            rw [hConnectedNComponent,connectedComponentIn_eq (hConnectedNComponent ▸ hCy)]
            exact connectedComponentIn_mem_nhds (mem_interior_iff_mem_nhds.mp hNInterior)
          · intro hy
            have hyC : y ∈ connectedN := interior_subset hy
            have hyN : y ∈ N := hConnectedNSubset hyC
            obtain ⟨x,hx,hxy⟩ := hRefinedImage ▸ hyN
            let xb : B := ⟨x,hx⟩
            have hComp : actualHalfHomeomorph xb ∈ connectedComponent (⟨base,hBaseN⟩ : N) := by
              rw [←hComponentImage] at hyC
              obtain ⟨w,hw,hwy⟩ := hyC
              have heq : actualHalfHomeomorph xb=w := Subtype.ext (hxy.trans hwy.symm)
              exact heq ▸ hw
            have hStrict : (1 : ℝ)/2 < ∑ v ∈ selected,x.val v := by
              apply lt_of_le_of_ne hx
              intro heq
              have hFront := hActualHalfFrontier x heq.symm
              rw [hxy] at hFront
              exact hFront.2 (interior_mono hConnectedNSubset hy)
            exact ⟨xb,⟨(hComponentIff xb).mpr hComp,hStrict⟩,hxy⟩
        have hMapContinuous : Continuous (fun x : B => realizationMap x.val) :=
          hRealizationEmbedding.continuous.comp continuous_subtype_val
        refine ⟨hEq ▸ hW.image _ hMapContinuous.continuousOn,?_⟩
        apply Set.Subset.antisymm
        · exact closure_minimal interior_subset hConnectedNCompact.isClosed
        · have hRawComponentImage : (fun x : B => realizationMap x.val) ''
              connectedComponent rawBase = connectedN := by
            ext y
            constructor
            · rintro ⟨x,hx,rfl⟩
              rw [←hComponentImage]
              exact ⟨actualHalfHomeomorph x,(hComponentIff x).mp hx,rfl⟩
            · intro hy
              rw [←hComponentImage] at hy
              obtain ⟨x,hx,hxy⟩ := hy
              refine ⟨actualHalfHomeomorph.symm x,?_,?_⟩
              · apply (hComponentIff _).mpr
                rw [actualHalfHomeomorph.apply_symm_apply]
                exact hx
              · have h := congrArg Subtype.val (actualHalfHomeomorph.apply_symm_apply x)
                exact h.trans hxy
          have h := image_closure_subset_closure_image hMapContinuous (s := W)
          have hClosure : closure W = connectedComponent rawBase :=
            OriginalHalfLevelInterior.actualStrictComponentClosure P selected rawBase
          rw [hClosure,hRawComponentImage,hEq] at h
          exact h
      have hActualConnectedNeighborhoodClassification :=
        LeanEval.Topology.ClassificationOfSurfaces.classification_of_surfaces connectedN
      have hNoActualSphereNeighborhood : ¬ Nonempty (connectedN ≃ₜ SphereRepresentative) := by
        rintro ⟨e⟩
        let f : SphereRepresentative → U := Subtype.val ∘ e.symm
        have hf : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp e.symm.isEmbedding
        have hn : ¬ IsCompact (Set.univ : Set U) := hCompact
        letI : Nonempty SphereRepresentative := ⟨PolygonCell.upperHemisphere (⟨0,by simp⟩ : PolygonCell 1)⟩
        have hopen : IsOpen (Set.range f) := by
          rw [isOpen_iff_forall_mem_open]
          rintro z ⟨x,rfl⟩
          let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
          have hgc : ContinuousOn (f ∘ e.symm) e.target :=
            hf.continuous.continuousOn.comp e.symm.continuousOn (fun _ _ => Set.mem_univ _)
          have hgi : Set.InjOn (f ∘ e.symm) e.target := by
            intro a ha b hb he
            exact e.symm.injOn ha hb (hf.injective he)
          have hgopen := CurveComplex.surface_invariance_of_domain_probe
            (f ∘ e.symm) e.target e.open_target hgc hgi
          refine ⟨(f ∘ e.symm) '' e.target,?_,hgopen,?_⟩
          · rintro y ⟨w,hw,rfl⟩
            exact ⟨e.symm w,rfl⟩
          · refine ⟨e x,e.map_source (mem_chart_source _ _),?_⟩
            simp only [Function.comp_apply,e.left_inv (mem_chart_source _ _)]
        have hcompact : IsCompact (Set.range f) := isCompact_range hf.continuous
        have hwhole : Set.range f = Set.univ :=
          IsClopen.eq_univ (⟨hcompact.isClosed,hopen⟩ : IsClopen (Set.range f)) (Set.range_nonempty f)
        exact hn (hwhole ▸ hcompact)
      have hActualConnectedBoundaryNormalForm :=
        hActualConnectedNeighborhoodClassification.resolve_left hNoActualSphereNeighborhood
      have hNoActualNonorientableNeighborhood (p n : ℕ) (hp : 1 ≤ p) :
          ¬ Nonempty (connectedN ≃ₜ Quot (NonOrientableRel p n)) := by
        rintro ⟨e⟩
        let f : Quot (NonOrientableRel p n) → U := fun x => (e.symm x : U)
        have hf : Topology.IsEmbedding f :=
          Topology.IsEmbedding.subtypeVal.comp e.symm.isEmbedding
        obtain ⟨a,b,hab,hOne⟩ :=
          actual_nonorientable_crosscap_embedding_has_single_crossing p n hp f hf
        have hEven := actualTransverseParity a b hab
        rw [hOne] at hEven
        norm_num at hEven
      have hActualConnectedOrientableNormalForm :
          ∃ p n : ℕ, (1 ≤ p ∨ 1 ≤ n) ∧
            Nonempty (connectedN ≃ₜ Quot (OrientableRel p n)) := by
        obtain ⟨p,n,hModel⟩ := hActualConnectedBoundaryNormalForm
        rcases hModel with hOrientable | hNonorientable
        · exact ⟨p,n,hOrientable⟩
        · exact False.elim (hNoActualNonorientableNeighborhood p n
            hNonorientable.1 hNonorientable.2)
      have hNoActualOrientablePositiveGenusNeighborhood (p n : ℕ) (hp : 1 ≤ p) :
          ¬ Nonempty (connectedN ≃ₜ Quot (OrientableRel p n)) := by
        rintro ⟨e⟩
        let f : Quot (OrientableRel p n) → U := fun x => (e.symm x : U)
        have hf : Topology.IsEmbedding f :=
          Topology.IsEmbedding.subtypeVal.comp e.symm.isEmbedding
        obtain ⟨a,b,hab,hOne⟩ :=
          actual_orientable_handle_embedding_has_single_crossing p n hp f hf
        have hEven := actualTransverseParity a b hab
        rw [hOne] at hEven
        norm_num at hEven
      have hActualConnectedGenusZeroNormalForm :
          ∃ n : ℕ, 1 ≤ n ∧ Nonempty (connectedN ≃ₜ Quot (OrientableRel 0 n)) := by
        obtain ⟨p,n,hpn,he⟩ := hActualConnectedOrientableNormalForm
        have hp0 : p=0 := by
          by_contra hp0
          exact hNoActualOrientablePositiveGenusNeighborhood p n (by omega) he
        subst p
        exact ⟨n,hpn.resolve_left (by omega),he⟩
      have hActualConnectedFrontierNullCurve (z : U) (hz : z ∈ frontier connectedN) :
          ∃ c : CurveComplex.Curve U, z ∈ c.image ∧
            (⟨c.map,c.embedded.continuous⟩ : C(Circle,U)).Nullhomotopic ∧
            c.image ⊆ frontier connectedN ∧ c.image ⊆ Kᶜ := by
        obtain ⟨c,hzc,hNull,hFrontier,hAvoid⟩ := hEveryFrontierPointOnNullCurve z (hConnectedNFrontier hz)
        have hzConnectedN : z ∈ connectedN :=
          hConnectedNCompact.isClosed.closure_eq ▸ frontier_subset_closure hz
        have hImageN : c.image ⊆ N := by
          intro x hx
          exact hNCompact.isClosed.closure_eq ▸ frontier_subset_closure (hFrontier hx)
        have hImageConnected : IsConnected c.image := isConnected_range c.embedded.continuous
        have hImageComponent : c.image ⊆ connectedN := by
          have hSub := hImageConnected.2.subset_connectedComponentIn hzc hImageN
          have hzComponent : z ∈ connectedComponentIn N base := hConnectedNComponent ▸ hzConnectedN
          rw [← connectedComponentIn_eq hzComponent] at hSub
          rw [hConnectedNComponent]
          exact hSub
        refine ⟨c,hzc,hNull,?_,hAvoid⟩
        intro x hx
        refine ⟨subset_closure (hImageComponent hx),?_⟩
        intro hxInterior
        exact (hFrontier hx).2 (interior_mono hConnectedNSubset hxInterior)
      have hActualConnectedFrontierCutParity (z : U) (hz : z ∈ frontier connectedN) :
          ∃ c : Curve U, z ∈ c.image ∧ c.image ⊆ frontier connectedN ∧
            Nonempty (CurveCutCover c) ∧
            ∀ (b : Curve U) (hab : Transverse c b), Even hab.1.toFinset.card := by
        obtain ⟨c,hzc,hNull,hFrontier,hAvoid⟩ := hActualConnectedFrontierNullCurve z hz
        exact ⟨c,hzc,hFrontier,actualCutCover c,
          fun b hab => actualTransverseParity c b hab⟩
      obtain ⟨J,hJ,hNJ,hBoundaryHull⟩ := hActualCompactBoundaryHomotopyHull
      refine ⟨connectedN,hConnectedNCompact,hKConnectedNInterior,hConnectedNInteriorRegular.1,hConnectedNInteriorRegular.2,
        hActualConnectedGenusZeroNormalForm,J,hJ,hConnectedNSubset.trans hNJ,?_⟩
      intro z hz
      obtain ⟨c,hzc,hFrontier,hAvoid,y,H,hH,V,hV,hCV,hFIff⟩ := hBoundaryHull z (hConnectedNFrontier hz)
      have hzConnectedN : z ∈ connectedN :=
        hConnectedNCompact.isClosed.closure_eq ▸ frontier_subset_closure hz
      have hImageN : c.image ⊆ N := by
        intro x hx
        exact hNCompact.isClosed.closure_eq ▸ frontier_subset_closure (hFrontier hx)
      have hImageConnected : IsConnected c.image := isConnected_range c.embedded.continuous
      have hImageComponent : c.image ⊆ connectedN := by
        have hSub := hImageConnected.2.subset_connectedComponentIn hzc hImageN
        have hzComponent : z ∈ connectedComponentIn N base := hConnectedNComponent ▸ hzConnectedN
        rw [← connectedComponentIn_eq hzComponent] at hSub
        rw [hConnectedNComponent]
        exact hSub
      have hcConnectedFrontier : c.image ⊆ frontier connectedN := by
        intro x hx
        refine ⟨subset_closure (hImageComponent hx),?_⟩
        intro hxInterior
        exact (hFrontier hx).2 (interior_mono hConnectedNSubset hxInterior)
      refine ⟨c,hzc,hcConnectedFrontier,hAvoid,y,H,hH,V,hV,hCV,?_⟩
      intro x hx
      constructor
      · intro hFront
        exact (hFIff x hx).mp (hConnectedNFrontier hFront)
      · intro hxc
        exact hcConnectedFrontier hxc
    have hEngulf : ∀ K : Set U, IsCompact K → ∃ D : Set U,
        IsCompact D ∧ Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ D) ∧
        K ⊆ interior D := by
      have actualNullCurveHomotopyCodomainRestriction {U : Type} [TopologicalSpace U]
          (M : Set U) (c : CurveComplex.Curve U) (y : U)
          (H : ContinuousMap.Homotopy
            (⟨c.map,c.embedded.continuous⟩ : C(Circle,U))
            (ContinuousMap.const Circle y)) (hH : Set.range H ⊆ M) :
          ∃ d : CurveComplex.Curve M,
            (∀ z : Circle, (d.map z : U)=c.map z) ∧
            (⟨d.map,d.embedded.continuous⟩ : C(Circle,M)).Nullhomotopic := by
        have hcM (z : Circle) : c.map z ∈ M := by
          have h := hH ⟨(0,z),rfl⟩
          have hzero : H (0,z)=c.map z := H.map_zero_left z
          rw [hzero] at h
          exact h
        have hyM : y ∈ M := by
          have h := hH ⟨(1,(1 : Circle)),rfl⟩
          have hone : H (1,(1 : Circle))=y := H.map_one_left 1
          rw [hone] at h
          exact h
        let cm : Circle → M := fun z => ⟨c.map z,hcM z⟩
        have hcm : Continuous cm := c.embedded.continuous.subtype_mk _
        have hce : IsEmbedding cm := IsEmbedding.of_comp hcm continuous_subtype_val c.embedded
        let d : CurveComplex.Curve M := ⟨cm,hce⟩
        let ym : M := ⟨y,hyM⟩
        let HM : ContinuousMap.Homotopy
            (⟨d.map,d.embedded.continuous⟩ : C(Circle,M))
            (ContinuousMap.const Circle ym) :=
          { toFun := fun p => ⟨H p,hH ⟨p,rfl⟩⟩
            continuous_toFun := H.continuous.subtype_mk _
            map_zero_left := by intro z; apply Subtype.ext; exact H.map_zero_left z
            map_one_left := by intro z; apply Subtype.ext; exact H.map_one_left z }
        exact ⟨d,fun _ => rfl,ym,⟨HM⟩⟩
      intro K hK
      obtain ⟨N,hN,hKN,hNInteriorConnected,hNRegularClosed,⟨n,hn,he⟩,J,hJ,hNJ,hBoundaryHull⟩ := hActualGenusZeroNeighborhood K hK
      by_cases hnOne : n=1
      · subst n
        obtain ⟨d,hdBoundary⟩ := CurveComplex.Hyperbolic.actual_zero_handle_one_boundary_model_closed_disc
        exact ⟨N,hN,⟨d.trans he.some.symm⟩,hKN⟩
      · have hnMany : 2 ≤ n := by omega
        obtain ⟨M,hM,hJM,hMInteriorConnected,hMRegularClosed,⟨m,hm,heM⟩,J',hJ',hMJ',hBoundaryHullM⟩ :=
          hActualGenusZeroNeighborhood J hJ
        have hNM : N ⊆ interior M := hNJ.trans hJM
        have hActualBoundaryHomotopyInsideM :
            ∀ z ∈ frontier N, ∃ c : CurveComplex.Curve U,
              z ∈ c.image ∧ c.image ⊆ frontier N ∧ c.image ⊆ Kᶜ ∧
              ∃ y : U, ∃ H : ContinuousMap.Homotopy
                (⟨c.map,c.embedded.continuous⟩ : C(Circle,U))
                (ContinuousMap.const Circle y), Set.range H ⊆ interior M := by
          intro z hz
          obtain ⟨c,hzc,hFrontier,hAvoid,y,H,hH,hIsolation⟩ := hBoundaryHull z hz
          exact ⟨c,hzc,hFrontier,hAvoid,y,H,hH.trans hJM⟩
        have hActualBoundaryNullCurveInM :
            ∀ z ∈ frontier N, ∃ d : CurveComplex.Curve M,
              z ∈ Subtype.val '' d.image ∧
              d.image ⊆ {x : M | (x : U) ∈ frontier N} ∧
              (⟨d.map,d.embedded.continuous⟩ : C(Circle,M)).Nullhomotopic := by
          intro z hz
          obtain ⟨c,hzc,hFrontier,hAvoid,y,H,hH⟩ := hActualBoundaryHomotopyInsideM z hz
          obtain ⟨d,hMap,hNull⟩ := actualNullCurveHomotopyCodomainRestriction
            M c y H (hH.trans interior_subset)
          refine ⟨d,?_,?_,hNull⟩
          · obtain ⟨t,ht⟩ := hzc
            exact ⟨d.map t,⟨t,rfl⟩,(hMap t).trans ht⟩
          · rintro x ⟨t,rfl⟩
            change (d.map t : U) ∈ frontier N
            rw [hMap t]
            exact hFrontier ⟨t,rfl⟩
        let eM : M ≃ₜ Quot (OrientableRel 0 m) := heM.some
        have hActualBoundaryNullCurveInOriginalModel :
            ∀ z ∈ frontier N, ∃ d : CurveComplex.Curve (Quot (OrientableRel 0 m)),
              z ∈ (fun x : Quot (OrientableRel 0 m) => (eM.symm x : U)) '' d.image ∧
              (⟨d.map,d.embedded.continuous⟩ : C(Circle,Quot (OrientableRel 0 m))).Nullhomotopic := by
          intro z hz
          obtain ⟨d,hzd,hFrontier,hNull⟩ := hActualBoundaryNullCurveInM z hz
          let c : CurveComplex.Curve (Quot (OrientableRel 0 m)) :=
            ⟨eM ∘ d.map,eM.isEmbedding.comp d.embedded⟩
          refine ⟨c,?_,?_⟩
          · obtain ⟨x,hx,hxz⟩ := hzd
            refine ⟨eM x,?_,?_⟩
            · obtain ⟨t,ht⟩ := hx
              exact ⟨t,congrArg eM ht⟩
            · simpa only [eM.symm_apply_apply] using hxz
          · exact hNull.comp_right ⟨eM,eM.continuous⟩
        have hActualOriginalBoundaryPlanarFilling
            (f : M → EuclideanSpace ℝ (Fin 2)) (hf : IsEmbedding f) :
            ∀ z ∈ frontier N, ∃ d : CurveComplex.Curve M,
              z ∈ Subtype.val '' d.image ∧
              d.image ⊆ {x : M | (x : U) ∈ frontier N} ∧
              ∃ c : CurveComplex.Curve (EuclideanSpace ℝ (Fin 2)),
                (∀ t : Circle, c.map t=f (d.map t)) ∧
                Schoenflies.inside c.image ⊆ Set.range f := by
          intro z hz
          obtain ⟨d,hzd,hdFrontier,y,hNull⟩ := hActualBoundaryNullCurveInM z hz
          obtain ⟨H⟩ := hNull
          let c : CurveComplex.Curve (EuclideanSpace ℝ (Fin 2)) :=
            ⟨f ∘ d.map,hf.comp d.embedded⟩
          let HP : ContinuousMap.Homotopy
              (⟨c.map,c.embedded.continuous⟩ : C(Circle,EuclideanSpace ℝ (Fin 2)))
              (ContinuousMap.const Circle (f y)) := {
            toFun := fun t => f (H t)
            continuous_toFun := hf.continuous.comp H.continuous
            map_zero_left := by
              intro t
              have ht : H (0,t)=d.map t := H.map_zero_left t
              exact congrArg f ht
            map_one_left := by
              intro t
              have ht : H (1,t)=y := H.map_one_left t
              exact congrArg f ht }
          refine ⟨d,hzd,hdFrontier,c,fun _ => rfl,?_⟩
          exact (CurveComplex.actual_planar_jordan_inside_subset_nullhomotopy_range c (f y) HP).trans
            (by rintro q ⟨t,rfl⟩; exact ⟨H t,rfl⟩)
        have hActualPlaneEmbeddedMEngulf
            (f : M → EuclideanSpace ℝ (Fin 2)) (hf : IsEmbedding f) :
            ∃ D : Set U, IsCompact D ∧
              Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ D) ∧
              K ⊆ interior D := by
          have hMInteriorNonempty : (interior M).Nonempty :=
            hNInteriorConnected.nonempty.mono (interior_subset.trans hNM)
          obtain ⟨E,hE,hEMap⟩ :=
            OriginalPartialPlaneEngulfing.actualEmbeddedNeighborhoodPartialPlaneChart M hMInteriorNonempty f hf
          apply OriginalPartialPlaneEngulfing.actualCompactNeighborhoodEngulfedInPartialPlaneChart
            E N K hN (by rw [hE]; exact hNM) hNInteriorConnected hNRegularClosed hKN
          intro z hz
          obtain ⟨c,hzc,hFrontier,hAvoid,y,H,hH,V,hV,hCV,hFIff⟩ := hBoundaryHull z hz
          refine ⟨c,hzc,hFrontier,y,H,?_,V,hV,hCV,hFIff⟩
          rw [hE]
          exact hH.trans hJM
        -- The original K engulfing geometry is now fully constructed from any actual plane embedding of its actual larger genus-zero neighborhood M.
        -- Exact sole remaining producer: actual raw genus-zero model embedding, for the actual m≥1 obtained by compact classification.
        have hActualOriginalGenusZeroModelPlanar :
            ∃ f : Quot (OrientableRel 0 m) → EuclideanSpace ℝ (Fin 2), IsEmbedding f := by
          by_cases hmOne : m=1
          · subst m
            obtain ⟨d,hd⟩ := CurveComplex.Hyperbolic.actual_zero_handle_one_boundary_model_closed_disc
            exact ⟨Subtype.val ∘ d.symm,IsEmbedding.subtypeVal.comp d.symm.isEmbedding⟩
          · have hmMany : 2 ≤ m := by omega
            exact CurveComplex.Hyperbolic.actual_genus_zero_boundary_model_embeds_plane m hm
        obtain ⟨f,hf⟩ := hActualOriginalGenusZeroModelPlanar
        exact hActualPlaneEmbeddedMEngulf (f ∘ eM) (hf.comp eM.isEmbedding)
    exact Or.inl (surface_plane_of_compact_disk_engulfing hEngulf)

#print axioms closed_surface_simply_connected_cover_plane_or_sphere
end CurveComplex.LocalSurgery
