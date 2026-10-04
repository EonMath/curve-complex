import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourEdgeJointConvexCellExtension
import Mathlib.Topology.Homotopy.Basic
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- A genuine joint convex-cell extension is connected to the specified original
and final fillings by constructed convex bridges, with exact matching stages. -/
theorem actual_convex_movie_endpoint_completion
    {X : Type} [TopologicalSpace X]
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (original final : C(X,V)) (middle : C(X × Interval,V)) :
    ∃ first : original.Homotopy
        (⟨fun x => middle (x,0),by fun_prop⟩ : C(X,V)),
    ∃ mid : (⟨fun x => middle (x,0),by fun_prop⟩ : C(X,V)).Homotopy
        (⟨fun x => middle (x,1),by fun_prop⟩ : C(X,V)),
    ∃ last : (⟨fun x => middle (x,1),by fun_prop⟩ : C(X,V)).Homotopy final,
    ∃ full : original.Homotopy final,
      full=(first.trans mid).trans last ∧
      (∀ σ x,mid (σ,x)=middle (x,σ)) ∧
      (∀ σ x,middle (x,0)=original x → first (σ,x)=original x) ∧
      (∀ σ x,middle (x,1)=final x → last (σ,x)=final x) := by
  let m0 : C(X,V) := ⟨fun x => middle (x,0),by fun_prop⟩
  let m1 : C(X,V) := ⟨fun x => middle (x,1),by fun_prop⟩
  let first : original.Homotopy m0 :=
    { toFun := fun z => ⟨(1-z.1.val) • (original z.2).val +
          z.1.val • (m0 z.2).val,
        hV (original z.2).property (m0 z.2).property
          (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring)⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp
      map_one_left := by intro x; apply Subtype.ext; simp }
  let mid : m0.Homotopy m1 :=
    { toFun := fun z => middle (z.2,z.1)
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; rfl
      map_one_left := by intro x; rfl }
  let last : m1.Homotopy final :=
    { toFun := fun z => ⟨(1-z.1.val) • (m1 z.2).val +
          z.1.val • (final z.2).val,
        hV (m1 z.2).property (final z.2).property
          (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring)⟩
      continuous_toFun := by fun_prop
      map_zero_left := by intro x; apply Subtype.ext; simp
      map_one_left := by intro x; apply Subtype.ext; simp }
  refine ⟨first,mid,last,(first.trans mid).trans last,rfl,?_,?_,?_⟩
  · intro σ x; rfl
  · intro σ x hx
    apply Subtype.ext
    change (1-σ.val) • (original x).val + σ.val • (middle (x,0)).val = _
    rw [hx,← add_smul]
    simp
  · intro σ x hx
    apply Subtype.ext
    change (1-σ.val) • (middle (x,1)).val + σ.val • (final x).val = _
    rw [hx,← add_smul]
    simp
end CurveComplex.HyperellipticModel
