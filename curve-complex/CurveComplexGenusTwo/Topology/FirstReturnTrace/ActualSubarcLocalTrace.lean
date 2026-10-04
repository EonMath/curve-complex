import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChart
import Mathlib.Topology.Order.IntermediateValue

namespace CurveComplex
open Set Topology Schoenflies

/-- An actual embedded subarc has the same local trace as its containing
embedded circle at every internal point. The neighbourhood is constructed by
one-dimensional intermediate values in a produced curve-adapted chart. -/
theorem source_subarc_local_trace_in_chart
    {S : Type} [TopologicalSpace S]
    (c : Curve S) (f : C(Interval,S)) (hf : IsEmbedding f)
    (hsub : Set.range f ⊆ c.image)
    (t : Interval) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1)
    (E : OpenPartialHomeomorph S Plane) (hp : f t ∈ E.source)
    (hflat : ∀ x ∈ E.source, x ∈ c.image ↔ E x 1 = 0) :
    ∃ U : Set S, IsOpen U ∧ f t ∈ U ∧ U ⊆ E.source ∧
      ∀ x ∈ U, x ∈ c.image ↔ x ∈ Set.range f := by
  let F : ℝ → S := fun u => f (projIcc 0 1 zero_le_one u)
  have hF : Continuous F := f.continuous.comp continuous_projIcc
  have hFt : F t = f t := by simp [F,projIcc_of_mem,t.property]
  have hopen : IsOpen (F ⁻¹' E.source) := E.open_source.preimage hF
  have htopen : (t:ℝ) ∈ F ⁻¹' E.source := by
    change F t ∈ E.source
    rw [hFt]
    exact hp
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp hopen t htopen
  let ε : ℝ := min (r/2) (min ((t:ℝ)/2) ((1-(t:ℝ))/2))
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by linarith))
  have hεr : ε < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεt : ε ≤ (t:ℝ)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεone : ε ≤ (1-(t:ℝ))/2 := (min_le_right _ _).trans (min_le_right _ _)
  let α : ℝ := (t:ℝ)-ε
  let β : ℝ := (t:ℝ)+ε
  have hαt : α < (t:ℝ) := by dsimp [α]; linarith
  have htβ : (t:ℝ) < β := by dsimp [β]; linarith
  have hαβ : α < β := hαt.trans htβ
  have hinterval : Set.Icc α β ⊆ Set.Icc (0:ℝ) 1 := by
    intro u hu
    dsimp [α,β] at hu
    constructor <;> linarith [hu.1,hu.2]
  have hsource : Set.MapsTo F (Set.Icc α β) E.source := by
    intro u hu
    apply hrsub
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [α,β] at hu
    constructor <;> linarith [hu.1,hu.2]
  let g : ℝ → ℝ := fun u => E (F u) 0
  have hg : ContinuousOn g (Set.Icc α β) :=
    (show Continuous (fun z : Plane => z 0) by fun_prop).continuousOn.comp
      (E.continuousOn.comp hF.continuousOn hsource) (fun _ _ => Set.mem_univ _)
  have hginj : Set.InjOn g (Set.Icc α β) := by
    intro u hu v hv he
    have hFu : F u ∈ c.image := hsub (Set.mem_range_self _)
    have hFv : F v ∈ c.image := hsub (Set.mem_range_self _)
    have hz1u := (hflat (F u) (hsource hu)).mp hFu
    have hz1v := (hflat (F v) (hsource hv)).mp hFv
    have heE : E (F u) = E (F v) := by
      ext j
      fin_cases j
      · exact he
      · exact hz1u.trans hz1v.symm
    have heF := E.injOn (hsource hu) (hsource hv) heE
    have heParam := hf.injective heF
    have heu : projIcc 0 1 zero_le_one u = ⟨u,hinterval hu⟩ := projIcc_of_mem _ _
    have hev : projIcc 0 1 zero_le_one v = ⟨v,hinterval hv⟩ := projIcc_of_mem _ _
    change projIcc 0 1 zero_le_one u = projIcc 0 1 zero_le_one v at heParam
    rw [heu,hev] at heParam
    exact congrArg Subtype.val heParam
  have htI : (t:ℝ) ∈ Set.Icc α β := ⟨hαt.le,htβ.le⟩
  have hαI : α ∈ Set.Icc α β := Set.left_mem_Icc.mpr hαβ.le
  have hβI : β ∈ Set.Icc α β := Set.right_mem_Icc.mpr hαβ.le
  let O : Set Plane := {z | min (g α) (g β) < z 0 ∧ z 0 < max (g α) (g β)}
  have hO : IsOpen O :=
    (isOpen_lt continuous_const (show Continuous (fun z : Plane => z 0) by fun_prop)).inter
      (isOpen_lt (show Continuous (fun z : Plane => z 0) by fun_prop) continuous_const)
  have htO : E (f t) ∈ O := by
    change min (g α) (g β) < E (f t) 0 ∧ E (f t) 0 < max (g α) (g β)
    rw [← hFt]
    change min (g α) (g β) < g t ∧ g t < max (g α) (g β)
    rcases hg.strictMonoOn_of_injOn_Icc' hαβ.le hginj with hm | hm
    · exact ⟨lt_of_le_of_lt (min_le_left _ _) (hm hαI htI hαt),
        lt_of_lt_of_le (hm htI hβI htβ) (le_max_right _ _)⟩
    · exact ⟨lt_of_le_of_lt (min_le_right _ _) (hm htI hβI htβ),
        lt_of_lt_of_le (hm hαI htI hαt) (le_max_left _ _)⟩
  let U := E.source ∩ E ⁻¹' O
  refine ⟨U,E.isOpen_inter_preimage hO,⟨hp,htO⟩,Set.inter_subset_left,?_⟩
  intro x hx
  constructor
  · intro hxc
    have hxO : E x ∈ O := hx.2
    have hxbetween : E x 0 ∈ Set.uIcc (g α) (g β) := by
      change min (g α) (g β) ≤ E x 0 ∧ E x 0 ≤ max (g α) (g β)
      exact ⟨hxO.1.le,hxO.2.le⟩
    have hximage : E x 0 ∈ g '' Set.Icc α β := by
      rcases le_total (g α) (g β) with hle | hle
      · apply intermediate_value_Icc hαβ.le hg
        simpa [Set.uIcc_of_le hle] using hxbetween
      · apply intermediate_value_Icc' hαβ.le hg
        simpa [Set.uIcc_of_ge hle] using hxbetween
    obtain ⟨u,hu,heu⟩ := hximage
    refine ⟨projIcc 0 1 zero_le_one u,?_⟩
    apply E.injOn (hsource hu) hx.1
    ext j
    fin_cases j
    · exact heu
    · exact ((hflat (F u) (hsource hu)).mp (hsub (Set.mem_range_self _))).trans
        ((hflat x hx.1).mp hxc).symm
  · exact fun hx => hsub hx

/-- Actual subarc/circle local agreement on the source surface, with no chart
or local-trace certificate supplied as a hypothesis. -/
theorem source_subarc_internal_local_trace
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (c : Curve S) (f : C(Interval,S)) (hf : IsEmbedding f)
    (hsub : Set.range f ⊆ c.image) (t : Interval)
    (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1)
    (W : Set S) (hW : IsOpen W) (hpW : f t ∈ W) :
    ∃ U : Set S, IsOpen U ∧ f t ∈ U ∧ U ⊆ W ∧
      ∀ x ∈ U, x ∈ c.image ↔ x ∈ Set.range f := by
  obtain ⟨E,hp,hzero,hEW,hsquare,hflat⟩ :=
    position_curve_crosscut_chart S c (f t) (hsub (Set.mem_range_self t)) W hW hpW
  obtain ⟨U,hU,hpU,hUE,htrace⟩ := source_subarc_local_trace_in_chart c f hf hsub t ht0 ht1 E hp hflat
  exact ⟨U,hU,hpU,hUE.trans hEW,htrace⟩

end CurveComplex
#print axioms CurveComplex.source_subarc_local_trace_in_chart
#print axioms CurveComplex.source_subarc_internal_local_trace
