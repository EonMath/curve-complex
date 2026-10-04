import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualExactStripInteriorOpenChart
namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology CurveComplex.LocalSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- The original crossing chart forces opposite literal inverse-strip normals.
The adapted chart is produced from BC; no normal sign flip is an input. -/
theorem actual_exact_strip_transverse_normal_signs_flip
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (γ : C(Interval,S)) (hinj : InjOn γ (Ioo 0 1)) (himage : range γ⊆b.val.image)
    (u : Interval) (hu : 0<u.val ∧ u.val < 1)
    (hcross : CrossesInDisk M a b (γ u))
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (haxis : ∀ z,BC z∈a.val.image ↔ z.2.val=0)
    (T : Set Interval) (hT : IsOpen T) (huT : u∈T)
    (Q : C(T,range BC)) (hQ : ∀ t : T,(Q t).val=γ t.val)
    (normal : C(T,ℝ))
    (hnormal : ∀ t : T,normal t=((hBC.toHomeomorph.symm (Q t)).2:ℝ))
    (hbound : ∀ t : T,0<((hBC.toHomeomorph.symm (Q t)).1:ℝ) ∧
      ((hBC.toHomeomorph.symm (Q t)).1:ℝ) < 1 ∧ -1<normal t ∧ normal t < 1) :
    ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
      u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
      ∃ hvT : v∈T,∃ hwT : w∈T,
        normal ⟨v,hvT⟩≠0 ∧ normal ⟨w,hwT⟩≠0 ∧
        ((0<normal ⟨v,hvT⟩) ↔ ¬(0<normal ⟨w,hwT⟩)) := by
  let zu := hBC.toHomeomorph.symm (Q ⟨u,huT⟩)
  have hzu : 0<zu.1.val ∧ zu.1.val < 1 ∧ -1<zu.2.val ∧ zu.2.val < 1 := by
    dsimp [zu]
    rw [← hnormal ⟨u,huT⟩]
    exact hbound ⟨u,huT⟩
  obtain ⟨C,hmem,hdecode,hvalue⟩ := actual_exact_strip_interior_open_chart M BC hBC zu hzu
  have hdecodeQ (t : T) : BC (hBC.toHomeomorph.symm (Q t))=γ t.val :=
    (congrArg Subtype.val (hBC.toHomeomorph.apply_symm_apply (Q t))).trans (hQ t)
  have hchart (t : T) : γ t.val∈C.source ∧ (C (γ t.val)).1=normal t := by
    have hb := hbound t
    have hb' : -1<((hBC.toHomeomorph.symm (Q t)).2:ℝ) ∧
        ((hBC.toHomeomorph.symm (Q t)).2:ℝ) < 1 := by simpa only [← hnormal] using hb.2.2
    constructor
    · rw [← hdecodeQ t]
      exact hmem _ hb.1 hb.2.1 hb'.1 hb'.2
    · rw [← hdecodeQ t,hvalue _ hb.1 hb.2.1 hb'.1 hb'.2]
      exact (hnormal t).symm
  have hCa (x : S) (hx : x∈C.source) : x∈a.val.image ↔ (C x).1=0 := by
    obtain ⟨z,hz,hCz⟩ := hdecode x hx
    rw [← hz,haxis]
    rw [← hz] at hCz
    rw [hCz]
  obtain ⟨d,hd,hflip⟩ := actual_marked_transverse_uncentered_axis_signs_flip
    M a b u hu γ hinj himage hcross C (hchart ⟨u,huT⟩).1 hCa
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hT u huT
  refine ⟨min d ε,lt_min hd hε,?_⟩
  intro v w hvlo hvhi hwlo hwhi
  have hvmem : v∈Metric.ball u ε := by
    rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,abs_lt]
    constructor <;> change _ < _
    · have hmin := min_le_right d ε
      linarith only [hvlo,hmin]
    · have h : v.val < u.val := hvhi
      linarith only [h,hε]
  have hwmem : w∈Metric.ball u ε := by
    rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,abs_lt]
    constructor
    · have h : u.val < w.val := hwlo
      linarith only [h,hε]
    · have hmin := min_le_right d ε
      linarith only [hwhi,hmin]
  have hvT := hball hvmem
  have hwT := hball hwmem
  refine ⟨hvT,hwT,?_⟩
  have hf := hflip v w (by have hmin := min_le_left d ε; linarith only [hvlo,hmin])
    hvhi hwlo (by have hmin := min_le_left d ε; linarith only [hwhi,hmin])
  simpa only [(hchart ⟨v,hvT⟩).2,(hchart ⟨w,hwT⟩).2] using hf
end CurveComplex.HyperellipticModel.ArcSurgery
