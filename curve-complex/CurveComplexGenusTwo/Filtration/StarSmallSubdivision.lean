import CurveComplexGenusTwo.Filtration.OpenVertexStarScale
import CurveComplexGenusTwo.Filtration.ComparisonSmallSingularChains

open CategoryTheory Topology Convexity
open scoped Simplicial
namespace CurveComplexGenusTwo.CWHurewicz

noncomputable local instance (n : ℕ) : MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace
    (fun t => (t.weights : Fin (n + 1) → ℝ))

theorem singularBarycentricIterateList_eventually_starSmall
    {V : Type} (K : AbstractSimplicialComplex V) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of (CurveComplex.RealizationPoint K))) _⦋n⦌ →₀ ℤ) :
    ∃ k : ℕ, ∀ y ∈ (singularBarycentricIterateList
      (TopCat.of (CurveComplex.RealizationPoint K)) n k c).support,
      ∃ v : V, (TopCat.toSSetObjEquiv
        (TopCat.of (CurveComplex.RealizationPoint K)) (.op ⦋n⦌) y) '' Set.univ ⊆
          CurveComplex.openVertexStar K v := by
  classical
  let X := TopCat.of (CurveComplex.RealizationPoint K)
  let fs : List C(StdSimplex ℝ (Fin (n + 1)), CurveComplex.RealizationPoint K) :=
    c.support.toList.map (fun x => TopCat.toSSetObjEquiv X (.op ⦋n⦌) x)
  obtain ⟨δ, hδ, hcover⟩ := CurveComplex.exists_uniform_openVertexStar_scale K n fs
  obtain ⟨k, hk⟩ := barycentricFlagIterate_eventually_small n δ hδ
  refine ⟨k, ?_⟩
  intro y hy
  obtain ⟨x, hx, ss, hlen, rfl⟩ :=
    singularBarycentricIterateList_support X n k c y hy
  have hfx : (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x) ∈ fs := by
    exact List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩
  let t : StdSimplex ℝ (Fin (n + 1)) := .single 0
  obtain ⟨v, hv⟩ := hcover _ hfx (barycentricFlagIterate n ss t)
  refine ⟨v, ?_⟩
  rintro z ⟨u, _, rfl⟩
  rw [singularFlagIterate_eval]
  apply hv
  refine ⟨barycentricFlagIterate n ss u, ?_, rfl⟩
  exact Metric.mem_ball.mpr (hk ss hlen u t)
end CurveComplexGenusTwo.CWHurewicz
