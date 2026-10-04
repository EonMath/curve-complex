import CurveComplexGenusTwo.Filtration.UniverseCarrierIteration
open CategoryTheory Topology Convexity
open scoped Simplicial
open CurveComplexGenusTwo.CWHurewicz
namespace CurveGenusTwo.Filtration.UniverseSubdivision
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable local instance (n : ℕ) : MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace
    (fun t => (t.weights : Fin (n + 1) → ℝ))

private abbrev Sing (X : TopCat.{u}) (n : ℕ) := (TopCat.toSSet.obj X) _⦋n⦌

/-- A singular simplex resulting from a specified list of subdivision flags. -/
noncomputable def singularFlagIterate (X : TopCat.{u}) (n : ℕ)
    (ss : List (Equiv.Perm (Fin (n + 1)))) (x : Sing X n) : Sing X n :=
  match ss with
  | [] => x
  | σ :: tail => barycentricFlagSingular X n σ (singularFlagIterate X n tail x)

theorem singularFlagIterate_eval (X : TopCat.{u}) (n : ℕ)
    (ss : List (Equiv.Perm (Fin (n + 1)))) (x : Sing X n)
    (t : StdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSetObjEquiv X (.op ⦋n⦌) (singularFlagIterate X n ss x)) t =
      (TopCat.toSSetObjEquiv X (.op ⦋n⦌) x)
        (barycentricFlagIterate n ss t) := by
  induction ss generalizing t with
  | nil => simp [singularFlagIterate, barycentricFlagIterate]
  | cons σ ss ih =>
      simp only [singularFlagIterate, barycentricFlagIterate, Function.comp_apply]
      simp only [barycentricFlagSingular, Equiv.apply_symm_apply,
        ContinuousMap.comp_apply]
      exact ih (barycentricFlag n σ t)

/-- Repeated application of the actual signed singular barycentric operator. -/
noncomputable def singularBarycentricIterateList (X : TopCat.{u}) (n : ℕ)
    (k : ℕ) (c : Sing X n →₀ ℤ) : Sing X n →₀ ℤ :=
  match k with
  | 0 => c
  | k + 1 => singularBarycentricFinsupp X n (singularBarycentricIterateList X n k c)

theorem singularBarycentricFinsupp_support (X : TopCat.{u}) (n : ℕ)
    (c : Sing X n →₀ ℤ) (y : Sing X n)
    (hy : y ∈ (singularBarycentricFinsupp X n c).support) :
    ∃ x ∈ c.support, ∃ σ : Equiv.Perm (Fin (n + 1)),
      y = barycentricFlagSingular X n σ x := by
  classical
  have hrepr : c = ∑ x ∈ c.support, Finsupp.single x (c x) := by
    simpa [Finsupp.sum] using (Finsupp.sum_single c).symm
  rw [hrepr, map_sum] at hy
  obtain ⟨x, hx, hyx⟩ := Finsupp.mem_support_finsetSum y hy
  have hsingle : Finsupp.single x (c x) = c x • Finsupp.single x 1 := by
    ext z
    by_cases hz : z = x <;> simp [hz]
  rw [hsingle, LinearMap.map_smul] at hyx
  have hy' : y ∈ (singularBarycentricFinsupp X n (Finsupp.single x 1)).support :=
    Finsupp.support_smul hyx
  rw [singularBarycentricFinsupp_single] at hy'
  obtain ⟨σ, -, hσ⟩ := Finsupp.mem_support_finsetSum y hy'
  have hσ' : y = barycentricFlagSingular X n σ x := by
    have hσ'' := Finsupp.support_smul hσ
    simpa using hσ''
  exact ⟨x, hx, σ, hσ'⟩

theorem singularBarycentricIterateList_support (X : TopCat.{u}) (n k : ℕ)
    (c : Sing X n →₀ ℤ) (y : Sing X n)
    (hy : y ∈ (singularBarycentricIterateList X n k c).support) :
    ∃ x ∈ c.support, ∃ ss : List (Equiv.Perm (Fin (n + 1))),
      ss.length = k ∧ y = singularFlagIterate X n ss x := by
  induction k generalizing y with
  | zero =>
      exact ⟨y, by simpa [singularBarycentricIterateList] using hy,
        [], rfl, by simp [singularFlagIterate]⟩
  | succ k ih =>
      have hy' : y ∈ (singularBarycentricFinsupp X n
          (singularBarycentricIterateList X n k c)).support := by
        simpa [singularBarycentricIterateList] using hy
      obtain ⟨z, hz, σ, rfl⟩ := singularBarycentricFinsupp_support X n _ y hy'
      obtain ⟨x, hx, ss, hlen, rfl⟩ := ih z hz
      exact ⟨x, hx, σ :: ss, by simp [hlen], rfl⟩

/-- Every finite singular chain becomes subordinate to the excision cover after
an actual iterated barycentric subdivision. -/
theorem singularBarycentricIterateList_eventually_starSmall
    {V : Type u} (K : AbstractSimplicialComplex V) (n : ℕ)
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

end CurveGenusTwo.Filtration.UniverseSubdivision
