import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Topology.ArcStraightening
namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_nonloop_planar_arc (M : HyperellipticModel E S) (a : NonLoopArc M) (z : S)
    (ha : z ∉ a.val.image) (e : {x : S // x ≠ z} ≃ₜ Plane) :
    IsArcBetween
      (Set.range (fun t : Interval => e ⟨a.val.map t,
        fun h => ha (h ▸ ⟨t, rfl⟩)⟩))
      (e ⟨a.val.map 0, fun h => ha (h ▸ ⟨0, rfl⟩)⟩)
      (e ⟨a.val.map 1, fun h => ha (h ▸ ⟨1, rfl⟩)⟩) := by
  let g : Interval → Plane := fun t => e ⟨a.val.map t,
    fun h => ha (h ▸ ⟨t, rfl⟩)⟩
  have hg : Continuous g := e.continuous.comp (a.val.continuous.subtype_mk _)
  have hi : Function.Injective g := by
    intro t u h
    apply a.injective
    exact congrArg Subtype.val (e.injective h)
  let f : ℝ → Plane := fun t => g (projIcc 0 1 (by norm_num) t)
  have hf : Continuous f := hg.comp continuous_projIcc
  refine ⟨f, hf.continuousOn, ?_, ?_, ?_, ?_⟩
  · intro t ht u hu h
    have he := hi h
    rw [projIcc_of_mem (by norm_num) ht, projIcc_of_mem (by norm_num) hu] at he
    exact congrArg Subtype.val he
  · ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨projIcc 0 1 (by norm_num) t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨t.val, t.property, ?_⟩
      dsimp [f]
      rw [projIcc_of_mem (by norm_num) t.property]
  · dsimp [f]
    rw [projIcc_of_mem (by norm_num) (by norm_num : (0 : ℝ) ∈ Icc 0 1)]
    rfl
  · dsimp [f]
    rw [projIcc_of_mem (by norm_num) (by norm_num : (1 : ℝ) ∈ Icc 0 1)]
    rfl

end CurveComplex.HyperellipticModel
