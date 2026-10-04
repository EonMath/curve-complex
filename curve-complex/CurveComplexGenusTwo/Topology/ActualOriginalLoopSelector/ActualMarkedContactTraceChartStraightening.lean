import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualRealContactTraceRangeStraightening
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopBaseAxisChartProof
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- An actual old-loop contact trace in the produced base chart constructs a
marked-relative straightening. It stays inside the EXISTING trace image;
no larger chart, convex target, branch selector, or homotopy is supplied. -/
theorem actual_marked_contact_trace_chart_straightening
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (U : Set S) (V : Set Plane) (e : U ≃ₜ V)
    (hmarks : Disjoint U ((M.cover.branch : Set S) \ {a.val.map 0}))
    (haxis : ∀ q : U,q.val ∈ a.val.image ↔ (e q).val 1=0)
    (hp : a.val.map 0 ∈ U) (hezero : (e ⟨a.val.map 0,hp⟩).val=0)
    (T : C(Icc (0:ℝ) (1/2),S)) (hTU : ∀ t,T t ∈ U)
    (hTzero : T ⟨0,le_rfl,by norm_num⟩=a.val.map 0)
    (hTold : ∀ t,T t ∈ a.val.image)
    (hTnz : ∀ t,0<t.val → T t≠a.val.map 0) :
    ∃ F : C(unitInterval × Icc (0:ℝ) (1/2),S),
      (∀ t,F (0,t)=T t) ∧
      (∀ σ,F (σ,⟨0,le_rfl,by norm_num⟩)=a.val.map 0) ∧
      (∀ σ,F (σ,⟨1/2,by norm_num,le_rfl⟩)=T ⟨1/2,by norm_num,le_rfl⟩) ∧
      (∀ z,F z ∈ range T) ∧ (∀ z,F z ∈ a.val.image) ∧
      (∀ z,0<z.2.val → F z ∉ (M.cover.branch : Set S)) ∧
      (∀ t (h : F (1,t) ∈ U),(e ⟨F (1,t),h⟩).val=
        (2*t.val) • (e ⟨T ⟨1/2,by norm_num,le_rfl⟩,hTU _⟩).val) := by
  let C : C(Icc (0:ℝ) (1/2),ℂ) :=
    ⟨fun t => ArcFinitePosition.planeComplexLinearEquiv (e ⟨T t,hTU t⟩).val,
      ArcFinitePosition.planeComplexLinearEquiv.continuous.comp
        (continuous_subtype_val.comp (e.continuous.comp (T.continuous.subtype_mk hTU)))⟩
  have hc0 : C ⟨0,le_rfl,by norm_num⟩=0 := by
    have hh : (⟨T ⟨0,le_rfl,by norm_num⟩,hTU _⟩ : U)=⟨a.val.map 0,hp⟩ :=
      Subtype.ext hTzero
    change ArcFinitePosition.planeComplexLinearEquiv (e ⟨T _,hTU _⟩).val=0
    rw [hh,hezero]; simp
  have hcreal (t) : (C t).im=0 := (haxis _).mp (hTold t)
  have hcnz (t) (ht : 0<t.val) : C t≠0 := by
    intro hz
    have hh : (e ⟨T t,hTU t⟩).val=0 :=
      by
        apply ArcFinitePosition.planeComplexLinearEquiv.injective
        change ArcFinitePosition.planeComplexLinearEquiv (e ⟨T t,hTU t⟩).val=0 at hz
        simpa only [map_zero] using hz
    have he : e ⟨T t,hTU t⟩=e ⟨a.val.map 0,hp⟩ := Subtype.ext (hh.trans hezero.symm)
    exact hTnz t ht (congrArg Subtype.val (e.injective he))
  obtain ⟨H,hH0,hH1,hHzero,hHend,hHreal,hHnz,hHrange⟩ :=
    actual_real_contact_trace_range_straightening C hc0 hcreal hcnz
  have hHV (z) : ArcFinitePosition.planeComplexLinearEquiv.symm (H z) ∈ V := by
    obtain ⟨t,ht⟩ := hHrange z
    rw [← ht]
    change ArcFinitePosition.planeComplexLinearEquiv.symm
      (ArcFinitePosition.planeComplexLinearEquiv (e ⟨T t,hTU t⟩).val) ∈ V
    simp only [ArcFinitePosition.planeComplexLinearEquiv.symm_apply_apply]
    exact (e ⟨T t,hTU t⟩).property
  let F : C(unitInterval × Icc (0:ℝ) (1/2),S) :=
    ⟨fun z => (e.symm ⟨ArcFinitePosition.planeComplexLinearEquiv.symm (H z),hHV z⟩).val,
      continuous_subtype_val.comp (e.symm.continuous.comp
        ((ArcFinitePosition.planeComplexLinearEquiv.symm.continuous.comp H.continuous).subtype_mk hHV))⟩
  have hcoord (z) : (e ⟨F z,(e.symm ⟨_,hHV z⟩).property⟩).val=
      ArcFinitePosition.planeComplexLinearEquiv.symm (H z) := by
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hrange (z) : F z ∈ range T := by
    obtain ⟨t,ht⟩ := hHrange z
    refine ⟨t,?_⟩
    have he : e ⟨T t,hTU t⟩=e ⟨F z,(e.symm ⟨_,hHV z⟩).property⟩ := by
      apply Subtype.ext
      rw [hcoord,← ht]
      exact (ArcFinitePosition.planeComplexLinearEquiv.symm_apply_apply _).symm
    exact congrArg Subtype.val (e.injective he)
  have hF0 (t) : F (0,t)=T t := by
    have he : e ⟨F (0,t),(e.symm ⟨_,hHV (0,t)⟩).property⟩=e ⟨T t,hTU t⟩ := by
      apply Subtype.ext
      rw [hcoord,hH0]
      exact ArcFinitePosition.planeComplexLinearEquiv.symm_apply_apply _
    exact congrArg Subtype.val (e.injective he)
  have hFzero (σ) : F (σ,⟨0,le_rfl,by norm_num⟩)=a.val.map 0 := by
    have he : e ⟨F (σ,⟨0,le_rfl,by norm_num⟩),(e.symm ⟨_,hHV _⟩).property⟩=e ⟨a.val.map 0,hp⟩ := by
      apply Subtype.ext
      rw [hcoord,hHzero,hezero]; simp
    exact congrArg Subtype.val (e.injective he)
  have hFend (σ) : F (σ,⟨1/2,by norm_num,le_rfl⟩)=T ⟨1/2,by norm_num,le_rfl⟩ := by
    have he : e ⟨F (σ,⟨1/2,by norm_num,le_rfl⟩),(e.symm ⟨_,hHV _⟩).property⟩=
        e ⟨T ⟨1/2,by norm_num,le_rfl⟩,hTU _⟩ := by
      apply Subtype.ext
      rw [hcoord,hHend]
      exact ArcFinitePosition.planeComplexLinearEquiv.symm_apply_apply _
    exact congrArg Subtype.val (e.injective he)
  refine ⟨F,hF0,hFzero,hFend,hrange,?_,?_,?_⟩
  · intro z
    obtain ⟨t,ht⟩ := hrange z
    exact ht ▸ hTold t
  · intro z ht hm
    have hFU : F z ∈ U := (e.symm ⟨_,hHV z⟩).property
    have hb : F z=a.val.map 0 := by
      by_contra hn
      exact Set.disjoint_left.mp hmarks hFU ⟨hm,fun hx => hn (mem_singleton_iff.mp hx)⟩
    have hc : ArcFinitePosition.planeComplexLinearEquiv.symm (H z)=0 := by
      calc
        _ = (e ⟨F z,hFU⟩).val := (hcoord z).symm
        _ = (e ⟨a.val.map 0,hp⟩).val := congrArg (fun q : U => (e q).val) (Subtype.ext hb)
        _ = 0 := hezero
    exact hHnz z ht (by simpa using congrArg ArcFinitePosition.planeComplexLinearEquiv hc)
  · intro t h
    rw [hcoord,hH1]
    rw [ArcFinitePosition.planeComplexLinearEquiv.symm.map_smul]
    congr 1
    exact ArcFinitePosition.planeComplexLinearEquiv.symm_apply_apply _
end CurveComplex.HyperellipticModel
