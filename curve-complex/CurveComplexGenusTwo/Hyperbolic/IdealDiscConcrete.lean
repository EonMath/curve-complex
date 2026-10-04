import CurveComplexGenusTwo.Hyperbolic.Cayley

namespace CurveComplex.Hyperbolic

open Topology

structure IdealDisc (B C : Type*) [TopologicalSpace B] [TopologicalSpace C] where
  interior : H2 → C
  ideal : B → C
  interior_embedded : IsEmbedding interior
  ideal_embedded : IsEmbedding ideal
  compact : CompactSpace C
  hausdorff : T2Space C
  disjoint : Set.range interior ∩ Set.range ideal = ∅
  cover : Set.range interior ∪ Set.range ideal = Set.univ
  standard_chart : C ≃ₜ Metric.closedBall (0 : ℂ) 1
  boundary_chart : B ≃ₜ Circle
  interior_is_cayley : ∀ z, standard_chart (interior z) = cayley z
  ideal_is_circle : ∀ b,
    ((standard_chart (ideal b) : Metric.closedBall (0 : ℂ) 1) : ℂ) =
      (boundary_chart b : ℂ)

noncomputable def idealCircle (b : Circle) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨(b : ℂ), by simp [Metric.mem_closedBall, dist_zero_right]⟩

theorem cayley_isEmbedding : IsEmbedding cayley := by
  apply (Topology.IsEmbedding.subtypeVal (p := fun z : ℂ =>
    z ∈ Metric.closedBall (0 : ℂ) 1)).of_comp_iff.mp
  exact (Topology.IsEmbedding.subtypeVal (p := fun z : ℂ =>
    z ∈ Metric.ball (0 : ℂ) 1)).comp cayleyHomeomorph.isEmbedding

theorem idealCircle_isEmbedding : IsEmbedding idealCircle := by
  apply (Topology.IsEmbedding.subtypeVal (p := fun z : ℂ =>
    z ∈ Metric.closedBall (0 : ℂ) 1)).of_comp_iff.mp
  exact Topology.IsEmbedding.subtypeVal

theorem cayley_idealCircle_disjoint :
    Set.range cayley ∩ Set.range idealCircle = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x ⟨⟨z, hz⟩, ⟨b, hb⟩⟩
  have hball : ‖(cayley z : ℂ)‖ < 1 := by
    change ‖((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)‖ < 1
    simpa only [Metric.mem_ball, dist_zero_right] using cayley_mem_ball z
  have hcoe : (cayley z : ℂ) = (b : ℂ) :=
    congrArg Subtype.val (hz.trans hb.symm)
  rw [hcoe, Circle.norm_coe] at hball
  linarith

theorem cayley_idealCircle_cover :
    Set.range cayley ∪ Set.range idealCircle = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hx : ‖(x : ℂ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  by_cases hball : (x : ℂ) ∈ Metric.ball (0 : ℂ) 1
  · left
    refine ⟨cayleyInverse ⟨x, hball⟩, ?_⟩
    apply Subtype.ext
    exact cayley_cayleyInverse ⟨x, hball⟩
  · right
    have hn : ‖(x : ℂ)‖ = 1 := by
      apply le_antisymm hx
      have : ¬ ‖(x : ℂ)‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hball
      exact le_of_not_gt this
    let b : Circle := ⟨(x : ℂ), by
      change (x : ℂ) ∈ Metric.sphere (0 : ℂ) 1
      simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    rfl

noncomputable def standardIdealDisc :
    IdealDisc Circle (Metric.closedBall (0 : ℂ) 1) where
  interior := cayley
  ideal := idealCircle
  interior_embedded := cayley_isEmbedding
  ideal_embedded := idealCircle_isEmbedding
  compact := inferInstance
  hausdorff := inferInstance
  disjoint := cayley_idealCircle_disjoint
  cover := cayley_idealCircle_cover
  standard_chart := Homeomorph.refl _
  boundary_chart := Homeomorph.refl _
  interior_is_cayley := fun _ => rfl
  ideal_is_circle := fun _ => rfl

end CurveComplex.Hyperbolic
