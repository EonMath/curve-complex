import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualSameAtlasUniformOrientationInternal
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualRelativeDeformationVanishing
import CurveComplexGenusTwo.Topology.ActualFiniteDiscDetection.FiniteWithSingletonCandidate

open scoped Manifold ContDiff Bundle
open Bundle Filter Topology Metric CategoryTheory CategoryTheory.Limits Set
open CurveComplex CurveComplexGenusTwo.CWHurewicz CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false

private theorem actual_literal_complex_closed_disc_relative_cap_class
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    let D := closedBall z₀ ρ;
    let B : Set D := {x | dist x.val z₀ = ρ};
    ∃ γ : C(Circle,B),
      (∀ z, ((γ z).val.val : ℂ) = z₀+(ρ:ℂ)*z) ∧
      ∃ r : relativeHomology D B 2,
        relativeConnecting D B 1 r =
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass := by
  run_tac do
    let n := Lean.Name.str (Lean.Name.num
      (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualComplexChartCoordinateCoherencePrivateCandidate") 0)
      "actual_literal_complex_closed_disc_relative_cap_class"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) _ _ (by assumption)))

private theorem actual_literal_scaled_circle_boundary_surjective
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (γ : C(Circle, {x : closedBall z₀ ρ | dist x.val z₀ = ρ}))
    (hγ : ∀ z, (γ z).val.val = z₀+(ρ:ℂ)*z) : Function.Surjective γ := by
  run_tac do
    let n := Lean.Name.str (Lean.Name.num
      (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualComplexChartCoordinateCoherencePrivateCandidate") 0)
      "actual_literal_scaled_circle_boundary_surjective"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) _ _ (by assumption) _ (by assumption)))

private theorem actual_literal_chart_boundary_has_disc_supported_relative_cap
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (q : E) (ρ : ℝ) (hρ : 0 < ρ)
    (htarget : closedBall ((chartAt ℂ q) q) ρ ⊆ (chartAt ℂ q).target)
    (P : Set E) (β : C(Circle,P))
    (hβ : ∀ z, (β z : E) = (chartAt ℂ q).symm ((chartAt ℂ q) q + (ρ:ℂ)*z)) :
    let D := closedBall ((chartAt ℂ q) q) ρ;
    let B : Set D := {x | dist x.val ((chartAt ℂ q) q) = ρ};
    ∃ (γ : C(Circle,B)) (fD : C(D,E)) (hpair : ∀ x ∈ B, fD x ∈ P) (rD : relativeHomology D B 2),
      (∀ z, (γ z).val.val = (chartAt ℂ q) q+(ρ:ℂ)*z) ∧
      (∀ d, fD d = (chartAt ℂ q).symm d.val) ∧
      (relativeConnecting D B 1 rD =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass) ∧
      relativeConnecting E P 1 (pairRelativeHomologyMap B P fD hpair 2 rD) =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom β)) CircleFundamentalCycle.fundamentalClass := by
  classical
  let D := closedBall ((chartAt ℂ q) q) ρ
  let B : Set D := {x | dist x.val ((chartAt ℂ q) q) = ρ}
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)
  obtain ⟨γ,hγ,rD,hδ⟩ := actual_literal_complex_closed_disc_relative_cap_class ((chartAt ℂ q) q) ρ hρ
  let fD : C(D,E) := ⟨fun d => (chartAt ℂ q).symm d.val,
    (chartAt ℂ q).symm.continuousOn.comp_continuous continuous_subtype_val (fun d => htarget d.property)⟩
  have hfγ (z : Circle) : fD (γ z).val = (β z : E) := by
    change (chartAt ℂ q).symm (γ z).val.val = (β z : E)
    rw [hγ]
    exact (hβ z).symm
  have hpair : ∀ x ∈ B, fD x ∈ P := by
    intro x hx
    obtain ⟨z,hz⟩ := actual_literal_scaled_circle_boundary_surjective _ ρ hρ γ hγ ⟨x,hx⟩
    have hxγ : (γ z).val = x := congrArg Subtype.val hz
    rw [← hxγ,hfγ]
    exact (β z).property
  have hcomp : TopCat.ofHom γ ≫ pairMapOnSubspace B P fD hpair = TopCat.ofHom β := by
    ext z
    exact hfγ z
  have hmaps : F.map (pairMapOnSubspace B P fD hpair)
      (F.map (TopCat.ofHom γ) CircleFundamentalCycle.fundamentalClass) =
      F.map (TopCat.ofHom β) CircleFundamentalCycle.fundamentalClass := by
    change (F.map (TopCat.ofHom γ) ≫ F.map (pairMapOnSubspace B P fD hpair))
      CircleFundamentalCycle.fundamentalClass = _
    rw [← F.map_comp,hcomp]
  have hn := congrArg (fun f => f rD) (relativeConnecting_natural B P fD hpair 1)
  change F.map (pairMapOnSubspace B P fD hpair) (relativeConnecting D B 1 rD) =
    relativeConnecting E P 1 (pairRelativeHomologyMap B P fD hpair 2 rD) at hn
  rw [hδ,hmaps] at hn
  exact ⟨γ,fD,hpair,rD,hγ,fun d => rfl,hδ,hn.symm⟩

set_option maxHeartbeats 6000000 in
private theorem actual_same_atlas_disjoint_chart_caps_uniform_global_class
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℂ) ∞ E := hA;
    ∀ (Z : Finset E) (ρ : Z → ℝ),
      (∀ q, 0 < ρ q) →
      (∀ q : Z, closedBall ((chartAt ℂ q.val) q.val) (ρ q) ⊆ (chartAt ℂ q.val).target) →
      Set.univ.Pairwise (fun q r : Z => Disjoint
        ((chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q))
        ((chartAt ℂ r.val).symm '' closedBall ((chartAt ℂ r.val) r.val) (ρ r))) →
      let P := (⋃ q : Z,
        (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ;
      ∃ (β : Z → C(Circle,P)) (r : relativeHomology E P 2)
        (caps : Z → relativeHomology E P 2) (k : ℤ),
        k ≠ 0 ∧ r = k • ∑ q : Z, caps q ∧ relativeConnecting E P 1 r = 0 ∧
        (∀ q z, (β q z : E) = (chartAt ℂ q.val).symm
          ((chartAt ℂ q.val) q.val + (ρ q : ℂ)*z)) ∧
        ∀ q, relativeConnecting E P 1 (caps q) =
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (β q)))
            CircleFundamentalCycle.fundamentalClass := by
  classical
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : ClosedSurface E := Classical.choice hg.2.1
  intro Z ρ hρ htarget hdisj
  dsimp only
  have horientation : ∃ (z : H E 2) (Φ : ∀ q : E, relativeHomology E ({q}ᶜ) 2 ⟶ H Circle 1)
      (k : ℤ), k ≠ 0 ∧ (∀ q, IsIso (Φ q)) ∧
      (∀ q, homologyToRelative E ({q}ᶜ) 2 z ≠ 0) ∧
      (∀ q, Φ q (homologyToRelative E ({q}ᶜ) 2 z) =
        k • CircleFundamentalCycle.fundamentalClass) ∧
      ∀ (p : E) (ρ : ℝ) (hρ : 0 < ρ)
        (htarget : closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target),
        let c := chartAt ℂ p;
        let D := closedBall (c p) ρ;
        let B : Set D := {x | dist x.val (c p) = ρ};
        ∀ (γ : C(Circle,B)) (hγ : ∀ z, (γ z).val.val = c p+(ρ:ℂ)*z)
          (rD : relativeHomology D B 2)
          (hrD : relativeConnecting D B 1 rD =
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom γ)) CircleFundamentalCycle.fundamentalClass)
          (m : C(D,E)) (hmlit : ∀ x, m x = c.symm x.val)
          (q : E) (hqp : q ∈ c.source) (hqdisc : dist (c q) (c p) < ρ),
          ∃ hB : ∀ x ∈ B, m x ∈ ({q}ᶜ : Set E),
            Φ q (pairRelativeHomologyMap B ({q}ᶜ) m hB 2 rD) =
              CircleFundamentalCycle.fundamentalClass := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualSameAtlasUniformOrientationInternal") 0)
        "actual_genus_two_same_atlas_common_orientation_with_caps"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `E) $(Lean.mkIdent `hg) $(Lean.mkIdent `A) $(Lean.mkIdent `hA)))
  obtain ⟨zGlobal,Φ,k,hk,hΦiso,hglobalnonzero,hcommon,hΦcaps⟩ := horientation
  have actual_disjoint_chart_discs_have_common_compact_exterior_boundary_loops
      (Z : Finset E) (ρ : Z → ℝ)
      (hpos : ∀ q, 0 < ρ q)
      (htarget : ∀ q : Z, closedBall ((chartAt ℂ q.val) q.val) (ρ q) ⊆ (chartAt ℂ q.val).target)
      (hdisj : Set.univ.Pairwise (fun q r : Z => Disjoint
        ((chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q))
        ((chartAt ℂ r.val).symm '' closedBall ((chartAt ℂ r.val) r.val) (ρ r)))) :
      let U (q : Z) : Set E := (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q);
      let P : Set E := (⋃ q : Z, U q)ᶜ;
      IsCompact P ∧ ∃ β : Z → C(Circle,P),
        (∀ q z, (β q z : E) = (chartAt ℂ q.val).symm
          ((chartAt ℂ q.val) q.val + (ρ q : ℂ) * z)) ∧
        (∀ q, Function.Injective (β q)) := by
    classical
    let U (q : Z) : Set E := (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q)
    let P : Set E := (⋃ q : Z, U q)ᶜ
    have hU (q : Z) : IsOpen (U q) :=
      (chartAt ℂ q.val).symm.isOpen_image_of_subset_source isOpen_ball
        (ball_subset_closedBall.trans (htarget q))
    have hcompact : IsCompact P := (isOpen_iUnion hU).isClosed_compl.isCompact
    let γ (q : Z) (z : Circle) : E := (chartAt ℂ q.val).symm
      ((chartAt ℂ q.val) q.val + (ρ q : ℂ) * z)
    have hnorm (q : Z) (z : Circle) :
        dist ((chartAt ℂ q.val) q.val + (ρ q : ℂ) * z) ((chartAt ℂ q.val) q.val) = ρ q := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (hpos q), Circle.norm_coe, mul_one]
    have hboundary (q : Z) (z : Circle) :
        (chartAt ℂ q.val) q.val + (ρ q : ℂ) * z ∈
          closedBall ((chartAt ℂ q.val) q.val) (ρ q) := by
      rw [mem_closedBall, hnorm]
    have hγcont (q : Z) : Continuous (γ q) :=
      (chartAt ℂ q.val).symm.continuousOn.comp_continuous (by fun_prop)
        (fun z => htarget q (hboundary q z))
    have hγP (q : Z) (z : Circle) : γ q z ∈ P := by
      intro hx
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
      by_cases hqr : q = r
      · subst r
        obtain ⟨w, hw, hweq⟩ := hr
        have heq : w = (chartAt ℂ q.val) q.val + (ρ q : ℂ) * z :=
          (chartAt ℂ q.val).symm.injOn (htarget q (ball_subset_closedBall hw))
            (htarget q (hboundary q z)) hweq
        have hwlt := mem_ball.mp hw
        rw [heq, hnorm] at hwlt
        exact (lt_irrefl _ hwlt)
      · have hqmem : γ q z ∈ (chartAt ℂ q.val).symm ''
            closedBall ((chartAt ℂ q.val) q.val) (ρ q) :=
          ⟨_,hboundary q z,rfl⟩
        have hrmem : γ q z ∈ (chartAt ℂ r.val).symm ''
            closedBall ((chartAt ℂ r.val) r.val) (ρ r) :=
          Set.image_mono ball_subset_closedBall hr
        exact Set.disjoint_left.mp (hdisj (Set.mem_univ q) (Set.mem_univ r) hqr) hqmem hrmem
    let β (q : Z) : C(Circle,P) := ⟨fun z => ⟨γ q z,hγP q z⟩, (hγcont q).subtype_mk (hγP q)⟩
    refine ⟨hcompact,β,fun q z => rfl,?_⟩
    intro q z w hzw
    have heq : γ q z = γ q w := congrArg Subtype.val hzw
    have hcoord := congrArg (chartAt ℂ q.val) heq
    change (chartAt ℂ q.val) ((chartAt ℂ q.val).symm _) =
      (chartAt ℂ q.val) ((chartAt ℂ q.val).symm _) at hcoord
    rw [(chartAt ℂ q.val).right_inv (htarget q (hboundary q z)),
      (chartAt ℂ q.val).right_inv (htarget q (hboundary q w))] at hcoord
    have hmul := add_left_cancel hcoord
    apply Subtype.ext
    exact mul_left_cancel₀ (by exact_mod_cast (hpos q).ne') hmul

  obtain ⟨hcompact,β,hβ,hβinj⟩ :=
    actual_disjoint_chart_discs_have_common_compact_exterior_boundary_loops Z ρ hρ htarget hdisj
  let P : Set E := (⋃ q : Z,
    (chartAt ℂ q.val).symm '' ball ((chartAt ℂ q.val) q.val) (ρ q))ᶜ
  have havoid (q : Z) : ∀ x ∈ P, x ≠ q.val := by
    intro x hx he
    apply hx
    apply Set.mem_iUnion.mpr
    refine ⟨q,(chartAt ℂ q.val) q.val,mem_ball_self (hρ q),?_⟩
    exact ((chartAt ℂ q.val).left_inv (mem_chart_source ℂ q.val)).trans he.symm
  let r := homologyToRelative E P 2 zGlobal
  have hrboundary : relativeConnecting E P 1 r = 0 := by
    obtain ⟨hzero,_⟩ := pairHomology_exact_at_relative E P 1
    exact congrArg (fun f => f zGlobal) hzero
  have hnat (q : Z) :
      pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 r =
      homologyToRelative E ({q.val}ᶜ) 2 zGlobal := by
    have hn := pairRelativeHomologyMap_commutes P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2
    have hid : HomologicalComplex.homologyMap
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map) (TopCat.ofHom (ContinuousMap.id E))) 2 = 𝟙 (H E 2) := by
      change HomologicalComplex.homologyMap
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map) (𝟙 (TopCat.of E))) 2 = _
      simp
      rfl
    rw [hid] at hn
    exact congrArg (fun f => f zGlobal) hn
  have hc (q : Z) := actual_literal_chart_boundary_has_disc_supported_relative_cap E q.val
    (ρ q) (hρ q) (htarget q) P (β q) (hβ q)
  choose γ f hpair rD hγ hflit hδD hδ using hc
  let caps (q : Z) := pairRelativeHomologyMap
    {x : closedBall ((chartAt ℂ q.val) q.val) (ρ q) |
      dist x.val ((chartAt ℂ q.val) q.val) = ρ q} P (f q) (hpair q) 2 (rD q)
  have hcpositive (q : Z) :
      Φ q.val (pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 (caps q)) =
      CircleFundamentalCycle.fundamentalClass := by
    obtain ⟨hB,hpos⟩ := hΦcaps q.val (ρ q) (hρ q) (htarget q)
      (γ q) (hγ q) (rD q) (hδD q) (f q) (hflit q) q.val (mem_chart_source ℂ q.val)
      (by simpa only [dist_self] using hρ q)
    let B : Set (closedBall ((chartAt ℂ q.val) q.val) (ρ q)) :=
      {x | dist x.val ((chartAt ℂ q.val) q.val) = ρ q}
    have hm := pairRelativeHomologyMap_comp B P ({q.val}ᶜ) (f q) (ContinuousMap.id E)
      (hpair q) (havoid q) 2
    have heq := congrArg (fun m => m (rD q)) hm
    change pairRelativeHomologyMap B ({q.val}ᶜ) (f q) hB 2 (rD q) =
      pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 (caps q) at heq
    rw [← heq]
    exact hpos
  have hpoint (q : Z) :
      pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 r =
      k • pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 (caps q) := by
    haveI : IsIso (Φ q.val) := hΦiso q.val
    apply (ModuleCat.mono_iff_injective (Φ q.val)).mp inferInstance
    rw [map_zsmul,hcpositive,hnat]
    exact hcommon q.val
  have hoff (q t : Z) (hqt : q ≠ t) :
      pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 (caps t) = 0 := by
    let B : Set (closedBall ((chartAt ℂ t.val) t.val) (ρ t)) :=
      {x | dist x.val ((chartAt ℂ t.val) t.val) = ρ t}
    have hav : ∀ x, f t x ≠ q.val := by
      intro x he
      have hqmem : q.val ∈ (chartAt ℂ q.val).symm '' closedBall ((chartAt ℂ q.val) q.val) (ρ q) :=
        ⟨_,mem_closedBall_self (hρ q).le,(chartAt ℂ q.val).left_inv (mem_chart_source ℂ q.val)⟩
      have htmem : f t x ∈ (chartAt ℂ t.val).symm '' closedBall ((chartAt ℂ t.val) t.val) (ρ t) :=
        ⟨x.val,x.property,(hflit t x).symm⟩
      rw [he] at htmem
      exact Set.disjoint_left.mp (hdisj (Set.mem_univ q) (Set.mem_univ t) hqt) hqmem htmem
    have hcomp := pairRelativeHomologyMap_comp B P ({q.val}ᶜ) (f t) (ContinuousMap.id E)
      (hpair t) (havoid q) 2
    have hzero := actual_pairRelativeHomologyMap_zero_of_range_in_subspace B ({q.val}ᶜ)
      ((ContinuousMap.id E).comp (f t)) (fun x hx => havoid q (f t x) (hpair t x hx)) hav 2
    rw [hzero] at hcomp
    exact (congrArg (fun m => m (rD t)) hcomp).symm
  have hdiag (q : Z) :
      pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 (∑ t : Z, caps t) =
      pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 (caps q) := by
    rw [map_sum]
    apply Finset.sum_eq_single q
    · intro t ht htq
      exact hoff q t htq.symm
    · simp
  have hdet : ∃ had : ∀ q : Z, ∀ x ∈ P, x ≠ q.val,
      Function.Injective (fun a : relativeHomology E P 2 => fun q : Z =>
        pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (had q) 2 a) := by
    run_tac do
      let n := Lean.Name.str (Lean.Name.num
        (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualFiniteDiscDetection") "FiniteWithSingletonCandidate") 0)
        "actual_disjoint_literal_chart_discs_relative_point_detection"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)
        $(Lean.mkIdent `E) $(Lean.mkIdent `Z) $(Lean.mkIdent `ρ)
        $(Lean.mkIdent `hρ) $(Lean.mkIdent `htarget) $(Lean.mkIdent `hdisj)))
  obtain ⟨had,hinj⟩ := hdet
  have hsum : r = k • ∑ q : Z, caps q := by
    apply hinj
    funext q
    change pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 r =
      pairRelativeHomologyMap P ({q.val}ᶜ) (ContinuousMap.id E) (havoid q) 2 (k • ∑ t : Z, caps t)
    rw [map_zsmul,hdiag]
    exact hpoint q
  exact ⟨β,r,caps,k,hk,hsum,hrboundary,hβ,hδ⟩

