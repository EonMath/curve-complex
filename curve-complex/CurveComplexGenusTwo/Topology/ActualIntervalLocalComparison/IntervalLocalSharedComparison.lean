import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.IntervalLocalBarycentricOne

open scoped Manifold ContDiff Bundle Simplicial
open Convexity CategoryTheory CurveComplexGenusTwo.CWHurewicz
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

set_option maxHeartbeats 1000000

theorem actualRegularPath_interval_in_incidentOpen {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (γ : ActualRegularPath E)
    (hface : actualRegularPathAsSingular γ ∈ actualFaceSet b) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toFun t ∈ actualIncidentOpen b i (actualRegularPathAsSingular γ) := by
  intro t ht
  let u := TopCat.stdSimplexHomeomorphI.{0}.symm ⟨t, ht⟩
  have hu := actualFace_image_in_incidentOpen b i hsmall
    (actualRegularPathAsSingular γ) hface u
  simpa [u, actualRegularPathAsSingular] using hu

theorem actualSharedEdge_equivalent_to_regular_face {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (γ : ActualRegularPath E)
    (hface : actualRegularPathAsSingular γ ∈ actualFaceSet b) :
    (⟨Finsupp.single γ 1 -
        actualSharedEdgeRegular b i hsmall
          (Finsupp.single (actualRegularPathAsSingular γ) 1),
      by
        change actualRegularChainBoundary _ = 0
        rw [map_sub]
        have h := actualRegularization_same_singular_chain_boundary
          (Finsupp.single (actualRegularPathAsSingular γ) 1)
          (Finsupp.single γ 1)
          (actualSharedEdgeRegular b i hsmall
            (Finsupp.single (actualRegularPathAsSingular γ) 1))
          0 (actualSharedEdgeCorrection b i hsmall
            (Finsupp.single (actualRegularPathAsSingular γ) 1))
          (by simp [actualRegularChainsToSingular, Finsupp.lmapDomain_apply])
          (actualSharedEdgeCorrection_single b i hsmall _ hface)
        rw [h]
        abel⟩ :
      ActualRegularOneCycles E) ∈
      intervalLocalNormalizedRelations (E := E) := by
  classical
  obtain ⟨τ, hτ, hyτ⟩ := Finset.mem_biUnion.mp hface
  let τ' : b.support := ⟨τ, hτ⟩
  let q := (i τ').q
  let c := (i τ').c
  let r := (i τ').r
  let x := (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ)
    (StdSimplex.single 0)
  let z : Metric.ball c r := ⟨(chartAt ℂ q) x,
    (hsmall τ' (StdSimplex.single 0)).2⟩
  apply actualChartBallRegularCycle_mem_relations q c r (i τ').target z
  · intro δ hδ t ht
    rcases Finset.mem_union.mp (Finsupp.support_sub hδ) with h | h
    · have hδγ : δ = γ := by simpa using h
      subst δ
      exact (actualIncidentOpen_subset_ball b i τ'
        (actualRegularPathAsSingular γ) hyτ
        (actualRegularPath_interval_in_incidentOpen b i hsmall γ hface t ht)).1
    · exact (actualSharedEdgeRegular_single_support_in_ball b i hsmall τ'
        (actualRegularPathAsSingular γ) hyτ δ h t).1
  · intro δ hδ t ht
    rcases Finset.mem_union.mp (Finsupp.support_sub hδ) with h | h
    · have hδγ : δ = γ := by simpa using h
      subst δ
      exact (actualIncidentOpen_subset_ball b i τ'
        (actualRegularPathAsSingular γ) hyτ
        (actualRegularPath_interval_in_incidentOpen b i hsmall γ hface t ht)).2
    · exact (actualSharedEdgeRegular_single_support_in_ball b i hsmall τ'
        (actualRegularPathAsSingular γ) hyτ δ h t).2

noncomputable def actualRegularSignedSubdivision {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularOneChains E →ₗ[ℤ] ActualRegularOneChains E :=
  Finsupp.linearCombination ℤ (fun γ =>
    Finsupp.single γ.leftHalf 1 -
      Finsupp.single γ.rightHalf.reverse 1)

theorem actualRegularSignedSubdivision_singular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (actualRegularChainsToSingular (E := E)).comp
        (actualRegularSignedSubdivision (E := E)) =
      (singularBarycentricFinsupp (TopCat.of E) 1).comp
        (actualRegularChainsToSingular (E := E)) := by
  apply Finsupp.lhom_ext
  intro γ n
  simp only [LinearMap.comp_apply]
  have hs : (Finsupp.single γ n : ActualRegularOneChains E) =
      n • Finsupp.single γ 1 := by simp
  rw [hs, map_smul, map_smul, map_smul, map_smul]
  congr 1
  simp only [actualRegularSignedSubdivision, Finsupp.linearCombination_single,
    one_smul, map_sub]
  simp [actualRegularChainsToSingular, Finsupp.lmapDomain_apply,
    actualBarycentricOne_single_regular γ]

theorem actualRegularSignedSubdivision_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    (actualRegularChainBoundary (E := E)).comp
        (actualRegularSignedSubdivision (E := E)) =
      actualRegularChainBoundary (E := E) := by
  apply Finsupp.lhom_ext
  intro γ n
  simp only [LinearMap.comp_apply]
  have hs : (Finsupp.single γ n : ActualRegularOneChains E) =
      n • Finsupp.single γ 1 := by simp
  rw [hs]
  simp only [map_smul]
  congr 1
  simp only [actualRegularSignedSubdivision, Finsupp.linearCombination_single,
    one_smul, map_sub, actualRegularChainBoundary_single]
  simp only [ActualRegularPath.leftHalf, ActualRegularPath.rightHalf,
    ActualRegularPath.reverse]
  norm_num

noncomputable def actualRegularSignedSubdivisionCycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularOneCycles E →ₗ[ℤ] ActualRegularOneCycles E :=
  LinearMap.codRestrict (ActualRegularOneCycles E)
    ((actualRegularSignedSubdivision (E := E)).domRestrict
      (ActualRegularOneCycles E)) (fun z => by
      change actualRegularChainBoundary
        (actualRegularSignedSubdivision z.1) = 0
      rw [← LinearMap.comp_apply,
        actualRegularSignedSubdivision_boundary]
      exact z.2)

noncomputable def actualRegularSignedSubdivisionDifference {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualRegularOneChains E →ₗ[ℤ] ActualRegularOneCycles E where
  toFun z := ⟨z - actualRegularSignedSubdivision z, by
    change actualRegularChainBoundary _ = 0
    rw [map_sub, ← LinearMap.comp_apply,
      actualRegularSignedSubdivision_boundary]
    abel⟩
  map_add' a b := by
    apply Subtype.ext
    change (a + b) - actualRegularSignedSubdivision (a + b) =
      (a - actualRegularSignedSubdivision a) +
        (b - actualRegularSignedSubdivision b)
    rw [map_add]
    abel
  map_smul' n a := by
    apply Subtype.ext
    change n • a - actualRegularSignedSubdivision (n • a) =
      n • (a - actualRegularSignedSubdivision a)
    rw [map_smul, smul_sub]

theorem actualRegularSignedSubdivisionDifference_mem_relations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (z : ActualRegularOneCycles E) :
    z - actualRegularSignedSubdivisionCycle z ∈
      intervalLocalNormalizedRelations (E := E) := by
  classical
  let R := intervalLocalNormalizedRelations (E := E)
  have hsingle (γ : ActualRegularPath E) :
      actualRegularSignedSubdivisionDifference
        (Finsupp.single γ 1) ∈ R := by
    have hsub : actualRegularSubdivisionCycle γ ∈ R :=
      actualNormalizedRelations_le_intervalLocal
        (Submodule.subset_span (Or.inr ⟨γ, rfl⟩))
    have hrev : actualRegularReverseCycle γ.rightHalf ∈ R :=
      Submodule.subset_span (Or.inl (Or.inr ⟨γ.rightHalf, rfl⟩))
    have heq : actualRegularSignedSubdivisionDifference
          (Finsupp.single γ 1) =
        actualRegularSubdivisionCycle γ +
          actualRegularReverseCycle γ.rightHalf := by
      apply Subtype.ext
      simp [actualRegularSignedSubdivision,
        actualRegularSignedSubdivisionDifference,
        actualRegularSubdivisionCycle, actualRegularReverseCycle]
      abel
    rw [heq]
    exact R.add_mem hsub hrev
  have hall (a : ActualRegularOneChains E) :
      actualRegularSignedSubdivisionDifference a ∈ R := by
    induction a using Finsupp.induction_linear with
    | zero =>
        simp only [map_zero]
        exact R.zero_mem
    | add a b ha hb =>
        rw [map_add]
        exact R.add_mem ha hb
    | single γ n =>
        have hs : (Finsupp.single γ n : ActualRegularOneChains E) =
          n • Finsupp.single γ 1 := by simp
        rw [hs, map_smul]
        exact R.smul_mem n (hsingle γ)
  convert hall z.1 using 1
  apply Subtype.ext
  rfl

noncomputable def actualRegularSignedIterate {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) : ActualRegularOneChains E →ₗ[ℤ] ActualRegularOneChains E :=
  match k with
  | 0 => LinearMap.id
  | k + 1 => actualRegularSignedSubdivision.comp (actualRegularSignedIterate k)

theorem actualRegularSignedIterate_singular {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (a : ActualRegularOneChains E) :
    actualRegularChainsToSingular (actualRegularSignedIterate k a) =
      singularBarycentricIterate (TopCat.of E) 1 k
        (actualRegularChainsToSingular a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change actualRegularChainsToSingular
        (actualRegularSignedSubdivision (actualRegularSignedIterate k a)) = _
      rw [show actualRegularChainsToSingular
          (actualRegularSignedSubdivision (actualRegularSignedIterate k a)) =
          singularBarycentricFinsupp (TopCat.of E) 1
            (actualRegularChainsToSingular (actualRegularSignedIterate k a)) from
        LinearMap.congr_fun (actualRegularSignedSubdivision_singular (E := E)) _]
      rw [ih]
      rfl

theorem actualRegularSignedIterate_boundary {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (a : ActualRegularOneChains E) :
    actualRegularChainBoundary (actualRegularSignedIterate k a) =
      actualRegularChainBoundary a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change actualRegularChainBoundary
        (actualRegularSignedSubdivision (actualRegularSignedIterate k a)) = _
      rw [show actualRegularChainBoundary
          (actualRegularSignedSubdivision (actualRegularSignedIterate k a)) =
          actualRegularChainBoundary (actualRegularSignedIterate k a) from
        LinearMap.congr_fun (actualRegularSignedSubdivision_boundary (E := E)) _]
      exact ih

theorem actualRegularSignedIterate_difference_mem_relations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (k : ℕ) (z : ActualRegularOneCycles E) :
    (⟨z.1 - actualRegularSignedIterate k z.1, by
      change actualRegularChainBoundary _ = 0
      rw [map_sub, actualRegularSignedIterate_boundary k z.1]
      exact sub_self _⟩ : ActualRegularOneCycles E) ∈
      intervalLocalNormalizedRelations (E := E) := by
  induction k with
  | zero =>
      convert (intervalLocalNormalizedRelations (E := E)).zero_mem using 1
      apply Subtype.ext
      simp [actualRegularSignedIterate]
  | succ k ih =>
      let zk : ActualRegularOneCycles E :=
        ⟨actualRegularSignedIterate k z.1, by
          change actualRegularChainBoundary _ = 0
          rw [actualRegularSignedIterate_boundary]
          exact z.2⟩
      have hstep := actualRegularSignedSubdivisionDifference_mem_relations zk
      have hsum := (intervalLocalNormalizedRelations (E := E)).add_mem ih hstep
      convert hsum using 1
      apply Subtype.ext
      change z.1 - actualRegularSignedSubdivision
          (actualRegularSignedIterate k z.1) =
        (z.1 - actualRegularSignedIterate k z.1) +
          (actualRegularSignedIterate k z.1 -
            actualRegularSignedSubdivision (actualRegularSignedIterate k z.1))
      abel

theorem actualSharedEdge_regular_chain_comparison {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (i : b.support → ActualChartBallIndex E)
    (hsmall : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ))
    (a : ActualRegularOneChains E)
    (hface : ∀ γ ∈ a.support,
      actualRegularPathAsSingular γ ∈ actualFaceSet b) :
    ∃ z : ActualRegularOneCycles E,
      z.1 = a - actualSharedEdgeRegular b i hsmall
        (actualRegularChainsToSingular a) ∧
      z ∈ intervalLocalNormalizedRelations (E := E) := by
  classical
  let z : ActualRegularOneCycles E :=
    ∑ γ ∈ a.support.attach, (a γ.1) •
      (⟨Finsupp.single γ.1 1 -
          actualSharedEdgeRegular b i hsmall
            (Finsupp.single (actualRegularPathAsSingular γ.1) 1), by
        change actualRegularChainBoundary _ = 0
        rw [map_sub]
        have h := actualRegularization_same_singular_chain_boundary
          (Finsupp.single (actualRegularPathAsSingular γ.1) 1)
          (Finsupp.single γ.1 1)
          (actualSharedEdgeRegular b i hsmall
            (Finsupp.single (actualRegularPathAsSingular γ.1) 1))
          0 (actualSharedEdgeCorrection b i hsmall
            (Finsupp.single (actualRegularPathAsSingular γ.1) 1))
          (by simp [actualRegularChainsToSingular, Finsupp.lmapDomain_apply])
          (actualSharedEdgeCorrection_single b i hsmall _
            (hface γ.1 γ.2))
        rw [h]
        abel⟩ : ActualRegularOneCycles E)
  have hz : z ∈ intervalLocalNormalizedRelations (E := E) := by
    dsimp [z]
    apply Submodule.sum_mem
    intro γ hγ
    exact (intervalLocalNormalizedRelations (E := E)).smul_mem _
      (actualSharedEdge_equivalent_to_regular_face b i hsmall γ.1
        (hface γ.1 γ.2))
  refine ⟨z, ?_, hz⟩
  have hrepr : a = ∑ γ ∈ a.support, a γ • Finsupp.single γ 1 := by
    conv_lhs => rw [← Finsupp.sum_single a]
    simp [Finsupp.sum, Finsupp.smul_single]
  conv_rhs => rw [hrepr]
  simp only [map_sum, map_smul]
  conv_rhs => rhs; rw [← Finset.sum_attach]
  conv_rhs => lhs; rw [← Finset.sum_attach]
  rw [← Finset.sum_sub_distrib]
  dsimp [z]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  simp [actualRegularChainsToSingular, Finsupp.lmapDomain_apply, smul_sub]

theorem actualChartSmallBoundary_faceSupported_mem_relations {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (b : ActualSingularTwoChains E)
    (hsmall : ∀ σ ∈ b.support, ∃ i : ActualChartBallIndex E,
      ∀ u : StdSimplex ℝ (Fin 3),
        (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) σ) u ∈
          actualChartBallCover i)
    (z : ActualRegularOneCycles E)
    (hboundary : singularBoundaryFinsupp (TopCat.of E) 1 b =
      actualRegularChainsToSingular z.1)
    (hface : ∀ γ ∈ z.1.support,
      actualRegularPathAsSingular γ ∈ actualFaceSet b) :
    z ∈ intervalLocalNormalizedRelations (E := E) := by
  classical
  let i : b.support → ActualChartBallIndex E :=
    fun τ => Classical.choose (hsmall τ.1 τ.2)
  have hi : ∀ τ : b.support, ∀ u : StdSimplex ℝ (Fin 3),
      (TopCat.toSSetObjEquiv (TopCat.of E) (.op ⦋2⦌) τ.1) u ∈
        actualChartBallCover (i τ) := by
    intro τ
    exact Classical.choose_spec (hsmall τ.1 τ.2)
  obtain ⟨a, haeq, ha⟩ :=
    actualSharedTwoChain_regularBoundary_mem_relations b i hi
  obtain ⟨d, hdeq, hd⟩ :=
    actualSharedEdge_regular_chain_comparison b i hi z.1 hface
  have hsum : d + a ∈ intervalLocalNormalizedRelations (E := E) :=
    (intervalLocalNormalizedRelations (E := E)).add_mem hd ha
  have hza : z = d + a := by
    apply Subtype.ext
    change z.1 = d.1 + a.1
    rw [hdeq, haeq, hboundary]
    abel
  rwa [hza]

end CanonicalDimensionTwo
