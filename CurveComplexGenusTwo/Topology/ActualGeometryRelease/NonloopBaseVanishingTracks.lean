import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingSymmetry
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedTwoSideDisk
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingAfterClosedReplacement
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
namespace CurveComplex.HyperellipticModel
open Set Topology
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_nonloop_prefix_produces_marked_base_vanishing_tracks
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (hb : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) b)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
      (P : Set S) (hP : IsClosed P) (hbase : b.val.map 0 ∈ P)
      (haxis : ∀ t : Interval, 0 < (t:ℝ) →
        b.val.map ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
          (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩ ∉ P) :
      ∃ E : Interval × Icc (-1:ℝ) 1 → S,
        IsEmbedding E ∧ (∀ t, E (t,⟨0,by norm_num⟩)=b.val.map t) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
      ∃ h : C(Interval,ℝ), h 0=0 ∧
        (∀ t, 0 ≤ h t ∧ h t ≤ ρ) ∧
        (∀ t : Interval, 0 < (t:ℝ) → 0 < h t) ∧
        (∀ t : Interval, (1/2:ℝ) ≤ (t:ℝ) → h t=ρ) ∧
      ∃ f : Bool → C(Interval,S),
        (∀ s t, ∃ v : Icc (-1:ℝ) 1,
          (v:ℝ)=(if s then (1:ℝ) else -1)*h t ∧
          f s t=E (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,v)) ∧
      ∀ s,
        IsEmbedding (f s) ∧ f s 0=b.val.map 0 ∧
        range (f s) ∩ P={b.val.map 0} ∧
        range (f s) ∩ b.val.image={b.val.map 0} := by
  letI : T2Space S := M.sphere.symm.t2Space
  letI := (actualSphereSmoothAtlas M).charts
  let A : C(Interval,S) := ⟨b.val.map,b.val.continuous⟩
  have hA : IsEmbedding A := (b.val.continuous.isClosedEmbedding
    (NonLoopArc.injective ⟨b.val,actualRepresentative_nonloop M b hb⟩)).isEmbedding
  obtain ⟨E,hE,hcenter,_⟩ := CurveComplex.source_whole_embedded_arc_strip A hA
    univ isOpen_univ (subset_univ _)
  let Z := Interval × Icc (-1:ℝ) 1
  let X : Interval → Z := fun t =>
    (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
      (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,⟨0,by norm_num⟩)
  have hX : Continuous X := by dsimp [X]; fun_prop
  let F : Set Z := E ⁻¹' P
  have hF : IsClosed F := hP.preimage hE.continuous
  have hzeroE : E (X 0)=b.val.map 0 := by
    have hx : X 0=(0,⟨0,by norm_num⟩) := by
      apply Prod.ext
      · apply Subtype.ext; simp [X]
      · rfl
    rw [hx,hcenter]; rfl
  have hzeroF : X 0 ∈ F := by
    change E (X 0) ∈ P
    rw [hzeroE]
    exact hbase
  have hFne : F.Nonempty := ⟨X 0,hzeroF⟩
  have haxisF (t : Interval) (ht : 0 < (t:ℝ)) : X t ∉ F := by
    change E (X t) ∉ P
    rw [hcenter]
    exact haxis t ht
  let d : Interval → ℝ := fun t => Metric.infDist (X t) F / 4
  have hd : Continuous d := ((Metric.continuous_infDist_pt F).comp hX).div_const 4
  have hdpos (t : Interval) (ht : 0 < (t:ℝ)) : 0 < d t :=
    div_pos ((hF.notMem_iff_infDist_pos hFne).mp (haxisF t ht)) (by norm_num)
  let T : Set Interval := {t | (1/2:ℝ) ≤ (t:ℝ)}
  have hT : IsCompact T := (isClosed_le continuous_const continuous_subtype_val).isCompact
  obtain ⟨δ,hδ,hδd⟩ := hT.exists_forall_le' hd.continuousOn
    (fun t ht => hdpos t (lt_of_lt_of_le (by norm_num) ht))
  let ρ := min δ (1/2)
  have hρ : 0 < ρ := lt_min hδ (by norm_num)
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρhalf : ρ ≤ 1/2 := min_le_right _ _
  let h : C(Interval,ℝ) := ⟨fun t => min ρ (d t),continuous_const.min hd⟩
  have hn (t : Interval) : 0 ≤ h t :=
    le_min hρ.le (div_nonneg Metric.infDist_nonneg (by norm_num))
  have hb (t : Interval) : h t ≤ ρ := min_le_left _ _
  have hp (t : Interval) (ht : 0 < (t:ℝ)) : 0 < h t := lt_min hρ (hdpos t ht)
  have hzero : h 0=0 := by
    change min ρ (Metric.infDist (X 0) F / 4)=0
    rw [Metric.infDist_zero_of_mem hzeroF,zero_div,min_eq_right hρ.le]
  have htail (t : Interval) (ht : (1/2:ℝ) ≤ (t:ℝ)) : h t=ρ :=
    min_eq_left (hρδ.trans (hδd t ht))
  let sign : Bool → ℝ := fun s => if s then 1 else -1
  have hsign (s : Bool) : |sign s|=1 := by cases s <;> norm_num [sign]
  let Y : Bool → Interval → Z := fun s t =>
    ((X t).1,⟨sign s*h t,abs_le.mp (by
      rw [abs_mul,hsign,one_mul,abs_of_nonneg (hn t)]
      exact (hb t).trans (hρhalf.trans (by norm_num)))⟩)
  have hY (s : Bool) : Continuous (Y s) := by dsimp [Y,sign,X]; fun_prop
  let f : Bool → C(Interval,S) := fun s => ⟨E ∘ Y s,hE.continuous.comp (hY s)⟩
  have f0 (s : Bool) : f s 0=b.val.map 0 := by
    have hy : Y s 0=X 0 := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext; change sign s*h 0=0; rw [hzero,mul_zero]
    change E (Y s 0)=_
    rw [hy,hzeroE]
  have hdist (s : Bool) (t : Interval) : dist (X t) (Y s t)=h t := by
    rw [Prod.dist_eq]
    simp only [Y,Subtype.dist_eq,Real.dist_eq,sub_self,abs_zero,zero_sub,
      abs_neg,abs_mul,hsign,one_mul,abs_of_nonneg (hn t),max_eq_right (hn t)]
    change max 0 |(0:ℝ)-sign s*h t|=h t
    simp only [zero_sub,abs_neg,abs_mul,hsign,one_mul,abs_of_nonneg (hn t),
      max_eq_right (hn t)]
  have hYP (s : Bool) (t : Interval) (ht : 0 < (t:ℝ)) : Y s t ∉ F := by
    apply Metric.notMem_of_dist_lt_infDist
    rw [hdist]
    have hsmall : h t ≤ Metric.infDist (X t) F / 4 := min_le_right _ _
    have hpositive : 0 < Metric.infDist (X t) F :=
      (hF.notMem_iff_infDist_pos hFne).mp (haxisF t ht)
    linarith
  refine ⟨E,hE,hcenter,ρ,hρ,hρhalf,h,hzero,fun t => ⟨hn t,hb t⟩,hp,htail,f,fun s t => ⟨(Y s t).2,rfl,rfl⟩,?_⟩
  intro s
  have hfinj : Function.Injective (f s) := by
    intro t u he
    have hh := congrArg (fun z : Z => (z.1:ℝ)) (hE.injective he)
    change β*(t:ℝ)=β*(u:ℝ) at hh
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hβ0) hh)
  refine ⟨((f s).continuous.isClosedEmbedding hfinj).isEmbedding,f0 s,?_,?_⟩
  · ext z
    constructor
    · rintro ⟨⟨t,rfl⟩,htP⟩
      have ht : t=0 := by
        apply Subtype.ext
        change (t:ℝ)=0
        by_contra hne
        exact hYP s t (lt_of_le_of_ne t.property.1 (Ne.symm hne)) htP
      rw [ht,f0 s]
      exact mem_singleton _
    · intro hz
      have he := mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨0,f0 s⟩,hbase⟩
  · ext z
    constructor
    · rintro ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
      have he : Y s t=(u,⟨0,by norm_num⟩) :=
        hE.injective (hu.symm.trans (hcenter u).symm)
      have hy : sign s*h t=0 := congrArg (fun q : Z => (q.2:ℝ)) he
      have ht : t=0 := by
        apply Subtype.ext
        change (t:ℝ)=0
        by_contra hne
        have htp := hp t (lt_of_le_of_ne t.property.1 (Ne.symm hne))
        cases s <;> norm_num [sign,ne_of_gt htp] at hy
      rw [ht,f0 s]
      exact mem_singleton _
    · intro hz
      have he := mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨0,f0 s⟩,mem_range_self _⟩

end CurveComplex.HyperellipticModel
