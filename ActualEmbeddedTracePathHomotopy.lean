import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homeomorph.Lemmas

namespace CurveComplex
open Set Topology
noncomputable section

/-- Actual interval coordinates construct a relative homotopy between any
two paths on a common embedded interval trace. No homotopy is assumed. -/
theorem actual_paths_on_embedded_interval_homotopic
    {X : Type} [TopologicalSpace X] (g : C(Interval,X)) (hg : IsEmbedding g)
    {x y : X} (α β : Path x y)
    (hα : range α ⊆ range g) (hβ : range β ⊆ range g) : α.Homotopic β := by
  let e := hg.toHomeomorph
  let ka : Interval → Interval := fun t => e.symm ⟨α t,hα (mem_range_self t)⟩
  let kb : Interval → Interval := fun t => e.symm ⟨β t,hβ (mem_range_self t)⟩
  have hka : Continuous ka := e.symm.continuous.comp (α.continuous.subtype_mk _)
  have hkb : Continuous kb := e.symm.continuous.comp (β.continuous.subtype_mk _)
  have hga (t : Interval) : g (ka t) = α t := congrArg Subtype.val
    (e.apply_symm_apply ⟨α t,hα (mem_range_self t)⟩)
  have hgb (t : Interval) : g (kb t) = β t := congrArg Subtype.val
    (e.apply_symm_apply ⟨β t,hβ (mem_range_self t)⟩)
  have he0 : ka 0 = kb 0 := hg.injective ((hga 0).trans
    (α.source.trans (β.source.symm.trans (hgb 0).symm)))
  have he1 : ka 1 = kb 1 := hg.injective ((hga 1).trans
    (α.target.trans (β.target.symm.trans (hgb 1).symm)))
  let k : Interval × Interval → Interval := fun z =>
    ⟨(1-(z.1:ℝ))*(ka z.2:ℝ)+(z.1:ℝ)*(kb z.2:ℝ),by
      change (1-(z.1:ℝ)) • (ka z.2:ℝ) + (z.1:ℝ) • (kb z.2:ℝ) ∈ Icc (0:ℝ) 1
      apply convex_Icc (0:ℝ) 1 (ka z.2).property (kb z.2).property
      · exact sub_nonneg.mpr z.1.property.2
      · exact z.1.property.1
      · ring⟩
  have hk : Continuous k := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub continuous_fst.subtype_val).mul
      (hka.comp continuous_snd).subtype_val).add
        (continuous_fst.subtype_val.mul (hkb.comp continuous_snd).subtype_val)
  have hk0 (t : Interval) : k (0,t) = ka t := by apply Subtype.ext; simp [k]
  have hk1 (t : Interval) : k (1,t) = kb t := by apply Subtype.ext; simp [k]
  have hkleft (τ : Interval) : k (τ,0) = ka 0 := by
    apply Subtype.ext
    simp only [k,he0]
    ring
  have hkright (τ : Interval) : k (τ,1) = ka 1 := by
    apply Subtype.ext
    simp only [k,he1]
    ring
  refine ⟨{
    toFun := fun z => g (k z)
    continuous_toFun := g.continuous.comp hk
    map_zero_left := fun t => (congrArg g (hk0 t)).trans (hga t)
    map_one_left := fun t => (congrArg g (hk1 t)).trans (hgb t)
    prop' := ?_ }⟩
  intro τ t ht
  rcases ht with rfl | ht
  · exact (congrArg g (hkleft τ)).trans (hga 0)
  · rw [mem_singleton_iff] at ht
    subst t
    exact (congrArg g (hkright τ)).trans (hga 1)
end
end CurveComplex
