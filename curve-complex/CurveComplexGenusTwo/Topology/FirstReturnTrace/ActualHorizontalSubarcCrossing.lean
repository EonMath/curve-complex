import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualTraceCapTransfer
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualGraphCrossing
namespace CurveComplex
open Set Topology Schoenflies

theorem source_horizontal_subarc_crossing
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (a d : Curve S) (f : C(Interval,S)) (hf : IsEmbedding f)
    (hsub : Set.range f ⊆ d.image) (t : Interval)
    (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1)
    (E : OpenPartialHomeomorph S Plane) (hsource : ∀ u, f u ∈ E.source)
    (h : ℝ) (hflat : ∀ u, E (f u) 1=h) (hp0 : E (f t) 0=0)
    (ha : ∀ x ∈ E.source, x ∈ a.image ↔ E x 0=0) : CrossesAt a d (f t) := by
  let g : ℝ → ℝ := fun u => E (f (projIcc 0 1 zero_le_one u)) 0
  have hg : ContinuousOn g (Set.Icc (0:ℝ) 1) :=
    (show Continuous (fun q : Plane => q 0) by fun_prop).continuousOn.comp
      (E.continuousOn.comp (f.continuous.comp continuous_projIcc).continuousOn
        (fun u _ => hsource _)) (fun _ _ => Set.mem_univ _)
  have hgval (u : Interval) : g u = E (f u) 0 := by
    simp [g,projIcc_of_mem,u.property]
  have hginj : Set.InjOn g (Set.Icc (0:ℝ) 1) := by
    intro u hu v hv he
    let u' : Interval := ⟨u,hu⟩
    let v' : Interval := ⟨v,hv⟩
    have he0 : E (f u') 0 = E (f v') 0 := by
      rw [← hgval u',← hgval v']; exact he
    have heE : E (f u')=E (f v') := by
      ext j
      fin_cases j
      · exact he0
      · exact (hflat u').trans (hflat v').symm
    exact congrArg Subtype.val (hf.injective (E.injOn (hsource u') (hsource v') heE))
  let O : Set Plane := {q | min (g 0) (g 1)< q 0 ∧ q 0 < max (g 0) (g 1)}
  have hO : IsOpen O := (isOpen_lt continuous_const (show Continuous (fun q : Plane => q 0) by fun_prop)).inter
    (isOpen_lt (show Continuous (fun q : Plane => q 0) by fun_prop) continuous_const)
  have htO : E (f t) ∈ O := by
    change min (g 0) (g 1)< E (f t) 0 ∧ E (f t) 0 < max (g 0) (g 1)
    rw [← hgval]
    rcases hg.strictMonoOn_of_injOn_Icc' zero_le_one hginj with hm | hm
    · exact ⟨lt_of_le_of_lt (min_le_left _ _) (hm (by simp) t.property ht0),
        lt_of_lt_of_le (hm t.property (by simp) ht1) (le_max_right _ _)⟩
    · exact ⟨lt_of_le_of_lt (min_le_right _ _) (hm t.property (by simp) ht1),
        lt_of_lt_of_le (hm (by simp) t.property ht0) (le_max_left _ _)⟩
  obtain ⟨U,hU,hpU,hUE,htrace⟩ := source_subarc_internal_local_trace S d f hf hsub t ht0 ht1
    E.source E.open_source (hsource t)
  let W : Set S := U ∩ (E.source ∩ E ⁻¹' O)
  have hW : IsOpen W := hU.inter (E.isOpen_inter_preimage hO)
  let F := E.restr W
  have hFs : F.source=E.source ∩ W := by simp [F,hW.interior_eq]
  have hpF : f t ∈ F.source := hFs.symm ▸ ⟨hsource t,hpU,hsource t,htO⟩
  apply source_continuous_graph_crossing a d F (f t) hpF hp0 (fun _ => h)
    continuous_const (hflat t)
  · intro x hx
    exact ha x (hFs.le hx).1
  · intro x hx
    have hxU : x ∈ U := (hFs.le hx).2.1
    have hxE : x ∈ E.source := (hFs.le hx).1
    change x ∈ d.image ↔ E x 1=h
    rw [htrace x hxU]
    constructor
    · rintro ⟨u,rfl⟩; exact hflat u
    · intro hx1
      have hxO : E x ∈ O := (hFs.le hx).2.2.2
      have hxbetween : E x 0 ∈ Set.uIcc (g 0) (g 1) := ⟨hxO.1.le,hxO.2.le⟩
      have himage : E x 0 ∈ g '' Set.Icc (0:ℝ) 1 := by
        rcases le_total (g 0) (g 1) with hle | hle
        · apply intermediate_value_Icc zero_le_one hg
          simpa [Set.uIcc_of_le hle] using hxbetween
        · apply intermediate_value_Icc' zero_le_one hg
          simpa [Set.uIcc_of_ge hle] using hxbetween
      obtain ⟨u,hu,he⟩ := himage
      refine ⟨⟨u,hu⟩,E.injOn (hsource _) hxE ?_⟩
      ext j
      fin_cases j
      · exact (hgval ⟨u,hu⟩).symm.trans he
      · exact (hflat _).trans hx1.symm
end CurveComplex
#print axioms CurveComplex.source_horizontal_subarc_crossing
