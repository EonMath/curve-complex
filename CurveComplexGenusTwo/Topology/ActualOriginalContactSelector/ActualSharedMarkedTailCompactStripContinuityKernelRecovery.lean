import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Path
namespace CurveComplex.LocalSurgery
open Set Topology Filter
theorem actualCompactStripConstantBoundaryTraceContinuousAt
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    (K : C(X × Y,Z)) (y₀ : Y) (c : Z)
    (hboundary : ∀ x,K (x,y₀)=c) (γ : Y → X) :
    ContinuousAt (fun y => K (γ y,y)) y₀ := by
  rw [ContinuousAt,show K (γ y₀,y₀)=c from hboundary _]
  apply Filter.tendsto_def.mpr
  intro U hU
  have hP : ∀ x∈(univ : Set X),∀ᶠ z : Y × X in 𝓝 (y₀,x),K (z.2,z.1)∈U := by
    intro x hx
    have hc : Continuous (fun z : Y × X => K (z.2,z.1)) :=
      K.continuous.comp (continuous_snd.prodMk continuous_fst)
    have hu : U∈𝓝 (K (x,y₀)) := by rw [hboundary];exact hU
    exact hc.continuousAt.eventually hu
  have hall := (isCompact_univ : IsCompact (univ : Set X)).eventually_forall_of_forall_eventually
    (x₀:=y₀) (P:=fun y x => K (x,y)∈U) hP
  exact hall.mono (fun y hy => hy (γ y) (mem_univ _))
theorem actualCompactStripConstantBoundaryTraceContinuous
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T1Space Y] [TopologicalSpace Z]
    (K : C(X × Y,Z)) (y₀ : Y) (c : Z)
    (hboundary : ∀ x,K (x,y₀)=c) (γ : Y → X)
    (hγ : ContinuousOn γ {y₀}ᶜ) :
    Continuous (fun y => K (γ y,y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y=y₀
  · subst y
    exact actualCompactStripConstantBoundaryTraceContinuousAt K y₀ c hboundary γ
  · exact K.continuous.continuousAt.comp
      ((hγ.continuousAt ((isClosed_singleton.isOpen_compl).mem_nhds hy)).prodMk continuousAt_id)
theorem actualCompactStripClosedContactPath
    {X Z : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Z]
    (K : C(X × unitInterval,Z)) (c : Z)
    (hboundary : ∀ x,K (x,0)=c) (γ : unitInterval → X)
    (hγ : ContinuousOn γ {(0 : unitInterval)}ᶜ)
    (A : Set Z) (hc : c∈A)
    (hcontact : ∀ t : unitInterval,t≠0 → K (γ t,t)∈A) :
    ∃ f : Path c (K (γ 1,1)),(∀ t,f t=K (γ t,t)) ∧ range f⊆A := by
  let f : Path c (K (γ 1,1)) :=
    { toFun := fun t => K (γ t,t)
      continuous_toFun := actualCompactStripConstantBoundaryTraceContinuous K 0 c hboundary γ hγ
      source' := hboundary _
      target' := rfl }
  refine ⟨f,fun _ => rfl,?_⟩
  rintro _ ⟨t,rfl⟩
  by_cases ht : t=0
  · subst t
    change K (γ 0,0)∈A
    rw [hboundary]
    exact hc
  · exact hcontact t ht
theorem actualCompactStripPuncturedContactPath
    {X Z : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Z]
    (K : C(X × unitInterval,Z)) (c : Z)
    (hboundary : ∀ x,K (x,0)=c) (x₀ : X)
    (γ : C({t : unitInterval // t≠0},X))
    (A : Set Z) (hc : c∈A)
    (hcontact : ∀ t : {t : unitInterval // t≠0},K (γ t,t.val)∈A) :
    ∃ f : Path c (K (γ ⟨1,by simp⟩,1)),
      (∀ t : {t : unitInterval // t≠0},f t.val=K (γ t,t.val)) ∧ range f⊆A := by
  classical
  let γ' : unitInterval → X := fun t => if h : t=0 then x₀ else γ ⟨t,h⟩
  have hγ' : ContinuousOn γ' {(0 : unitInterval)}ᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    have he : (fun t : {t : unitInterval // t≠0} => γ' t.val)=
        (fun t : {t : unitInterval // t≠0} => γ ⟨t.val,t.property⟩) := by
      funext t
      exact dif_neg t.property
    change Continuous (fun t : {t : unitInterval // t≠0} => γ' t.val)
    rw [he]
    exact γ.continuous.comp (continuous_subtype_val.subtype_mk fun t => t.property)
  obtain ⟨f,hf,hrange⟩ := actualCompactStripClosedContactPath K c hboundary γ' hγ' A hc
    (fun t ht => by simpa only [γ',dif_neg ht] using hcontact ⟨t,ht⟩)
  have htarget : K (γ' 1,1)=K (γ ⟨1,by simp⟩,1) := by simp [γ']
  refine ⟨f.cast rfl htarget.symm,?_,?_⟩
  · intro t
    change f t.val=K (γ t,t.val)
    rw [hf]
    simp only [γ',dif_neg t.property]
  · exact hrange
end CurveComplex.LocalSurgery
