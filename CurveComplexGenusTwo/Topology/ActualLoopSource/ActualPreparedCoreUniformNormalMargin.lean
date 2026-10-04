import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopFiniteCoreSupport
import Mathlib.Topology.Order.Compact
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The existing compact selected common-strip support produces a uniform
positive normal-coordinate margin. No uniform margin is assumed. -/
theorem actual_prepared_core_uniform_normal_margin
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    (T A : Set X) (hA : IsClosed A) (hAT : A ⊆ T)
    (ψ : C(T,ℝ)) (hψ : ∀ x,ψ x<1) :
    ∃ δ : ℝ,0<δ ∧ ∀ x (hx : x ∈ A),ψ ⟨x,hAT hx⟩+δ<1 := by
  classical
  by_cases hne : A.Nonempty
  · let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
    let f : C(A,ℝ) := ⟨fun x => ψ ⟨x.val,hAT x.property⟩,
      ψ.continuous.comp (continuous_subtype_val.subtype_mk (fun x => hAT x.property))⟩
    have hfrange : (range f).Nonempty := by
      obtain ⟨x,hx⟩ := hne
      exact ⟨f ⟨x,hx⟩,mem_range_self _⟩
    obtain ⟨p,hp,hmax⟩ := (isCompact_range f.continuous).exists_isMaxOn hfrange
      (continuous_id : Continuous (id : ℝ → ℝ)).continuousOn
    obtain ⟨x,hx⟩ := hp
    have hp1 : p<1 := hx ▸ hψ ⟨x.val,hAT x.property⟩
    refine ⟨(1-p)/2,by linarith only [hp1],?_⟩
    intro y hy
    have hle : ψ ⟨y,hAT hy⟩≤p := hmax (mem_range_self (⟨y,hy⟩ : A))
    linarith only [hp1,hle]
  · refine ⟨1,by norm_num,?_⟩
    intro x hx
    exact False.elim (hne ⟨x,hx⟩)
end CurveComplex.HyperellipticModel
