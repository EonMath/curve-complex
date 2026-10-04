import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic

open scoped Manifold ContDiff Bundle Topology
open Bundle

theorem actual_global_bump_stage
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [T2Space E] [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q : E) (f : SmoothBumpFunction 𝓘(ℝ,ℂ) q)
    (V : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hV : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (V x))) (c : ℂ) :
    let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q;
    let V' : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x :=
      fun x => V x + f x • e.symmL ℝ x c;
    ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (V' x)) ∧
    ∀ x ∈ (chartAt ℂ q).source,
      (e (TotalSpace.mk' ℂ x (V' x))).2 =
        (e (TotalSpace.mk' ℂ x (V x))).2 + f x • c := by
  let e := trivializationAt ℂ (fun x : E => TangentSpace 𝓘(ℝ,ℂ) x) q
  let V' : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x :=
    fun x => V x + f x • e.symmL ℝ x c
  have hframe : ContMDiffOn 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (e.symmL ℝ x c)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff]
    apply contMDiffOn_const.congr
    intro x hx
    change (e ⟨x, e.symmL ℝ x c⟩).2 = c
    rw [e.symmL_apply hx]
    rw [e.mk_symm hx c]
    exact congrArg Prod.snd
      (e.apply_symm_apply (show (x,c) ∈ e.target from by simpa [e] using hx))
  have hsupported : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (f x • e.symmL ℝ x c)) := by
    apply ContMDiffOn.smul_section_of_tsupport
      (u := e.baseSet) (s := fun x => e.symmL ℝ x c)
    · exact f.contMDiff.contMDiffOn
    · exact e.open_baseSet
    · simpa only [e, TangentBundle.trivializationAt_baseSet] using
        f.tsupport_subset_chartAt_source
    · exact hframe
  constructor
  · exact hV.add_section hsupported
  · intro x hx
    have hbase : x ∈ e.baseSet := by simpa [e] using hx
    change (e ⟨x, V x + f x • e.symmL ℝ x c⟩).2 =
      (e ⟨x, V x⟩).2 + f x • c
    rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase]
    rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase]
    simp only [map_add, map_smul, e.continuousLinearMapAt_symmL hbase]

#print axioms actual_global_bump_stage
