import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
namespace CurveComplex.HyperellipticModel
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_RestrictedLinkLabelsHeaders_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
theorem actualRestrictedLink_fresh_labels (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (τ : Finset (EssentialArcClass M)) (hτ : τ ∈ actualRestrictedLink M T) :
    (∀ w ∈ τ, ¬ (actualArcLabels M).isLoop w) ∧
    (∀ w ∈ τ, ∀ z ∈ T.val ∪ τ, z ≠ w →
      ¬ (actualArcLabels M).isLoop z → classEndpoints M z ≠ classEndpoints M w) := by
  classical
  change Disjoint T.val τ ∧ T.val ∪ τ ∈ actualA M ∧
    badVertices (actualArcLabels M) (T.val ∪ τ) = T.val at hτ
  have good : ∀ w ∈ τ, w ∉ badVertices (actualArcLabels M) (T.val ∪ τ) := by
    intro w hw
    rw [hτ.2.2]
    exact fun hwT => Finset.disjoint_left.mp hτ.1 hwT hw
  have nonloop : ∀ w ∈ τ, ¬ (actualArcLabels M).isLoop w := by
    intro w hw hl
    exact good w hw (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hw, Or.inl hl⟩)
  refine ⟨nonloop, ?_⟩
  intro w hw z hz hzw hzl he
  exact good w hw (Finset.mem_filter.mpr
    ⟨Finset.mem_union_right _ hw, Or.inr ⟨z, hz, hzw, nonloop w hw, hzl, he⟩⟩)
end CurveComplex.HyperellipticModel
