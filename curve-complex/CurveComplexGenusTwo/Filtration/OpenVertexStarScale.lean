import CurveComplexGenusTwo.Foundations.EdgeHomotopy
open CategoryTheory Topology Convexity
open scoped Simplicial
namespace CurveComplex
universe u
variable {V : Type u}
noncomputable local instance (n : ℕ) : MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace
    (fun t => (t.weights : Fin (n + 1) → ℝ))
-- Producer C: one common star-cover scale for finite chain support.
-- Reviewed proposition; proof remains an explicit obligation.
theorem exists_uniform_openVertexStar_scale :
  ∀ (K : AbstractSimplicialComplex V) (n : ℕ)
    (fs : List C(StdSimplex ℝ (Fin (n + 1)), RealizationPoint K)),
  ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ fs, ∀ x : StdSimplex ℝ (Fin (n + 1)),
    ∃ v : V, f '' Metric.ball x δ ⊆ openVertexStar K v := by
  intro K n fs
  have single (f : C(StdSimplex ℝ (Fin (n + 1)), RealizationPoint K)) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : StdSimplex ℝ (Fin (n + 1)),
        ∃ v : V, f '' Metric.ball x δ ⊆ openVertexStar K v := by
    let c : V → Set (StdSimplex ℝ (Fin (n + 1))) :=
      fun v => f ⁻¹' openVertexStar K v
    have hopen : ∀ v, IsOpen (c v) :=
      fun v => (openVertexStar_isOpen K v).preimage f.continuous
    have hcover : Set.univ ⊆ ⋃ v, c v := by
      intro x _
      obtain ⟨v, hv⟩ := exists_mem_openVertexStar K (f x)
      exact Set.mem_iUnion.mpr ⟨v, hv⟩
    obtain ⟨δ, hδ, hballs⟩ :=
      lebesgue_number_lemma_of_metric isCompact_univ hopen hcover
    refine ⟨δ, hδ, fun x => ?_⟩
    obtain ⟨v, hv⟩ := hballs x (Set.mem_univ x)
    exact ⟨v, Set.image_subset_iff.mpr hv⟩
  induction fs with
  | nil => exact ⟨1, by norm_num, by simp⟩
  | cons f fs ih =>
      obtain ⟨δf, hδf, hf⟩ := single f
      obtain ⟨δs, hδs, hs⟩ := ih
      refine ⟨min δf δs, lt_min hδf hδs, ?_⟩
      intro g hg x
      rcases List.mem_cons.mp hg with rfl | hg
      · obtain ⟨v, hv⟩ := hf x
        exact ⟨v, (Set.image_mono
          (Metric.ball_subset_ball (min_le_left _ _))).trans hv⟩
      · obtain ⟨v, hv⟩ := hs g hg x
        exact ⟨v, (Set.image_mono
          (Metric.ball_subset_ball (min_le_right _ _))).trans hv⟩
end CurveComplex
