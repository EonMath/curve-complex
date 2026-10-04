import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import CurveComplexGenusTwo.Dictionary.Genus

open scoped Manifold ContDiff Bundle
open Bundle


private theorem actual_chart_constant_tangent_frame_smooth
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] (q : E) (v : ℂ) :
    let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q;
    ContMDiffOn 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (e.symmL ℝ x v)) e.baseSet := by
  let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q
  rw [e.contMDiffOn_section_baseSet_iff]
  have hconstant : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (fun _ : E => v) e.baseSet :=
    contMDiffOn_const
  apply hconstant.congr
  intro x hx
  change (e ⟨x, e.symmL ℝ x v⟩).2 = v
  rw [e.symmL_apply hx]
  rw [e.mk_symm hx v]
  exact congrArg Prod.snd (e.apply_symm_apply (show (x,v) ∈ e.target from by simpa [e] using hx))

theorem actual_supported_tangent_frame_smooth
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q : E) (v : ℂ) (f : SmoothBumpFunction 𝓘(ℝ,ℂ) q) :
    let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q;
    ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (f x • e.symmL ℝ x v)) := by
  let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q
  apply ContMDiffOn.smul_section_of_tsupport
    (u := e.baseSet) (s := fun x => e.symmL ℝ x v)
  · exact f.contMDiff.contMDiffOn
  · exact e.open_baseSet
  · simpa only [e, TangentBundle.trivializationAt_baseSet] using
      f.tsupport_subset_chartAt_source
  · exact actual_chart_constant_tangent_frame_smooth q v

private theorem actual_supported_tangent_frame_nonzero_at_center
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q : E) (f : SmoothBumpFunction 𝓘(ℝ,ℂ) q) :
    let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q;
    f q • e.symmL ℝ q (1 : ℂ) ≠ 0 := by
  let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q
  change f q • e.symmL ℝ q (1 : ℂ) ≠ 0
  rw [f.eq_one, one_smul]
  intro hz
  have hq : q ∈ e.baseSet := by simpa [e] using mem_chart_source ℂ q
  have he := congrArg (e.continuousLinearMapAt ℝ q) hz
  rw [e.continuousLinearMapAt_symmL hq, map_zero] at he
  exact one_ne_zero he

private theorem actual_supported_tangent_frame_nonzero_where_one
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q x : E) (f : SmoothBumpFunction 𝓘(ℝ,ℂ) q) (hf : f x = 1) :
    let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q;
    f x • e.symmL ℝ x (1 : ℂ) ≠ 0 := by
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  change f x • e.symmL ℝ x (1 : ℂ) ≠ 0
  rw [hf, one_smul]
  intro hz
  have hx : x ∈ e.baseSet := by
    simpa [e] using f.support_subset_source (by simp [hf] : x ∈ Function.support f)
  have he := congrArg (e.continuousLinearMapAt ℝ x) hz
  rw [e.continuousLinearMapAt_symmL hx, map_zero] at he
  exact one_ne_zero he

private theorem actual_supported_tangent_frame_spans_where_one
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q x : E) (f : SmoothBumpFunction 𝓘(ℝ,ℂ) q) (hf : f x = 1)
    (w : TangentSpace 𝓘(ℝ,ℂ) x) :
    let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q;
    ∃ a b : ℝ,
      w = a • (f x • e.symmL ℝ x (1 : ℂ)) +
          b • (f x • e.symmL ℝ x Complex.I) := by
  let e := trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) q
  change ∃ a b : ℝ,
    w = a • (f x • e.symmL ℝ x (1 : ℂ)) +
        b • (f x • e.symmL ℝ x Complex.I)
  have hx : x ∈ e.baseSet := by
    simpa [e] using f.support_subset_source (by simp [hf] : x ∈ Function.support f)
  let z : ℂ := e.continuousLinearMapAt ℝ x w
  have hz : (z.re : ℝ) • (1 : ℂ) + z.im • Complex.I = z := by
    apply Complex.ext <;> simp
  refine ⟨z.re, z.im, ?_⟩
  rw [hf, one_smul, one_smul]
  calc
    w = e.symmL ℝ x z := (e.symmL_continuousLinearMapAt hx w).symm
    _ = e.symmL ℝ x (z.re • (1 : ℂ) + z.im • Complex.I) := by rw [hz]
    _ = z.re • e.symmL ℝ x (1 : ℂ) + z.im • e.symmL ℝ x Complex.I := by
      rw [map_add, map_smul, map_smul]

private theorem actual_same_atlas_finite_smooth_tangent_field_cover
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := by
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      apply isManifold_of_contDiffOn
      intro e e' he he'
      have hh := StructureGroupoid.compatible (contDiffGroupoid ∞ 𝓘(ℂ)) he he'
      rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hh
      simpa only [contDiffPregroupoid, mfld_simps] using hh.1.restrict_scalars ℝ
    ∃ (ι : Type) (V W : ι → ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x),
      Finite ι ∧
      (∀ i, ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (V i x))) ∧
      (∀ i, ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (W i x))) ∧
      ∀ x, ∃ i, ∀ w : TangentSpace 𝓘(ℝ,ℂ) x,
        ∃ a b : ℝ, w = a • V i x + b • W i x := by
  letI : ChartedSpace ℂ E := A
  let : IsManifold 𝓘(ℂ) ∞ E := hA
  let : IsManifold 𝓘(ℝ,ℂ) ∞ E := by
    apply isManifold_of_contDiffOn
    intro e e' he he'
    have hh := StructureGroupoid.compatible (contDiffGroupoid ∞ 𝓘(ℂ)) he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hh
    simpa only [contDiffPregroupoid, mfld_simps] using hh.1.restrict_scalars ℝ
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  obtain ⟨ι, f, hf⟩ := SmoothBumpCovering.exists_isSubordinate
    𝓘(ℝ,ℂ) (s := Set.univ) (U := fun q : E => (chartAt ℂ q).source)
    isClosed_univ (by
      intro x _
      exact (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  let V (i : ι) (x : E) : TangentSpace 𝓘(ℝ,ℂ) x :=
    (f i x) • (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (f.c i)).symmL
      ℝ x (1 : ℂ)
  let W (i : ι) (x : E) : TangentSpace 𝓘(ℝ,ℂ) x :=
    (f i x) • (trivializationAt ℂ (fun y : E => TangentSpace 𝓘(ℝ,ℂ) y) (f.c i)).symmL
      ℝ x Complex.I
  letI : Fintype ι := f.fintype
  refine ⟨ι, V, W, inferInstance, ?_, ?_, ?_⟩
  · intro i
    exact actual_supported_tangent_frame_smooth (f.c i) 1 (f i)
  · intro i
    exact actual_supported_tangent_frame_smooth (f.c i) Complex.I (f i)
  · intro x
    let i := f.ind x (Set.mem_univ x)
    refine ⟨i, fun w => ?_⟩
    exact actual_supported_tangent_frame_spans_where_one (f.c i) x (f i)
      (f.apply_ind x (Set.mem_univ x)) w

#print axioms actual_same_atlas_finite_smooth_tangent_field_cover

theorem actual_same_atlas_finite_compact_bump_cores
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℝ,ℂ) ∞ E := by
      letI : IsManifold 𝓘(ℂ) ∞ E := hA
      apply isManifold_of_contDiffOn
      intro e e' he he'
      have hh := StructureGroupoid.compatible (contDiffGroupoid ∞ 𝓘(ℂ)) he he'
      rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hh
      simpa only [contDiffPregroupoid, mfld_simps] using hh.1.restrict_scalars ℝ
    ∃ (ι : Type) (f : SmoothBumpCovering ι 𝓘(ℝ,ℂ) E Set.univ),
      Finite ι ∧
      (∀ i, IsCompact {x : E | f i x = 1}) ∧
      (∀ i, {x : E | f i x = 1} ⊆ (chartAt ℂ (f.c i)).source) ∧
      ∀ x : E, ∃ i, f i x = 1 := by
  letI : ChartedSpace ℂ E := A
  let : IsManifold 𝓘(ℂ) ∞ E := hA
  let : IsManifold 𝓘(ℝ,ℂ) ∞ E := by
    apply isManifold_of_contDiffOn
    intro e e' he he'
    have hh := StructureGroupoid.compatible (contDiffGroupoid ∞ 𝓘(ℂ)) he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hh
    simpa only [contDiffPregroupoid, mfld_simps] using hh.1.restrict_scalars ℝ
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  obtain ⟨ι, f, hf⟩ := SmoothBumpCovering.exists_isSubordinate
    𝓘(ℝ,ℂ) (s := Set.univ) (U := fun q : E => (chartAt ℂ q).source)
    isClosed_univ (by
      intro x _
      exact (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  letI : Fintype ι := f.fintype
  refine ⟨ι, f, inferInstance, ?_, ?_, ?_⟩
  · intro i
    exact (isClosed_eq (f i).continuous continuous_const).isCompact
  · intro i x hx
    exact f.mem_chartAt_source_of_eq_one hx
  · intro x
    exact ⟨f.ind x (Set.mem_univ x), f.apply_ind x (Set.mem_univ x)⟩
