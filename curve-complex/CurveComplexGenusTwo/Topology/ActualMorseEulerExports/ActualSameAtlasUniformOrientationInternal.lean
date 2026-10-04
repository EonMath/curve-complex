import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.SingletonRelativeDetection
import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualComplexChartCoordinateCoherencePrivateCandidate
import CurveComplexGenusTwo.Topology.Orientation.SurfaceTopHomologyDetection
import CurveComplexGenusTwo.Topology.Orientation.SurfaceLocalization
import Mathlib.Topology.Connected.Clopen

open scoped Manifold ContDiff Bundle
open Bundle Filter Topology Metric CategoryTheory CategoryTheory.Limits Set
open CurveComplex CurveComplexGenusTwo.CWHurewicz CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false

private theorem actual_closed_surface_global_nonzero_top_class_has_nonzero_localizations
    (E : Type) [TopologicalSpace E] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    [ClosedSurface E] (z : H E 2) (hz : z ≠ 0) :
    ∀ x : E, homologyToRelative E ({x}ᶜ : Set E) 2 z ≠ 0 := by
  intro x hx
  have hc : IsClopen {y : E | homologyToRelative E ({y}ᶜ : Set E) 2 z = 0} :=
    ⟨surface_localization_zero_locus_closed E 2 z,
      homology_localization_zero_locus_open E 2 z⟩
  have hu := hc.eq_univ ⟨x,hx⟩
  apply hz
  apply surface_top_homology_detection E z
  intro y
  exact (Set.ext_iff.mp hu y).mpr (Set.mem_univ y)

private theorem actual_genus_two_global_top_class_nonzero_at_every_point
    (E : Type) [TopologicalSpace E] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : IsGenus E 2) :
    ∃ z : H E 2, z ≠ 0 ∧ ∀ x : E, homologyToRelative E ({x}ᶜ : Set E) 2 z ≠ 0 := by
  classical
  letI : ClosedSurface E := Classical.choice hg.2.1
  let e := Classical.choice hg.2.2.1
  let z : H E 2 := e.inv (1 : ℤ)
  have hz : z ≠ 0 := by
    intro hzero
    have h := congrArg e.hom hzero
    have hid : e.hom z = (1 : ℤ) := e.inv_hom_id_apply 1
    rw [map_zero, hid] at h
    exact one_ne_zero h
  exact ⟨z,hz,actual_closed_surface_global_nonzero_top_class_has_nonzero_localizations E z hz⟩


set_option maxHeartbeats 6000000 in
private theorem actual_genus_two_same_atlas_common_orientation_with_caps
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    letI : ChartedSpace ℂ E := A;
    letI : IsManifold 𝓘(ℂ) ∞ E := hA;
    ∃ (z : H E 2) (Φ : ∀ q : E, relativeHomology E ({q}ᶜ) 2 ⟶ H Circle 1)
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
  classical
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  letI : ClosedSurface E := Classical.choice hg.2.1
  exact (open Filter Topology Metric CategoryTheory CategoryTheory.Limits Set CurveComplex CurveComplex.Octagon CurveComplexGenusTwo.CWHurewicz CurveComplex.GenusOrientationCandidate in by
    have actual_literal_complex_closed_disc_relative_cap_class
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
    have actual_supplied_atlas_coherent_orientation_normalizes_all_literal_caps
    :
        ∃ Φ : ∀ q : E, relativeHomology E ({q}ᶜ) 2 ⟶ H Circle 1,
          (∀ q, IsIso (Φ q)) ∧
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
          (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "ActualComplexChartCoordinateCoherencePrivateCandidate") 0)
          "actual_supplied_atlas_coherent_orientation_normalizes_all_literal_caps"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n)))

    obtain ⟨Φ,hΦiso,hΦallLiteralCaps⟩ := actual_supplied_atlas_coherent_orientation_normalizes_all_literal_caps
    obtain ⟨zGlobal,hzGlobal,hActualGlobalLocalizationsNonzero⟩ :=
      actual_genus_two_global_top_class_nonzero_at_every_point E hg
    let kPoint (q : E) : ℤ :=
      -(CircleHomologyComputation.circleH1Iso.hom
        (Φ q (homologyToRelative E ({q}ᶜ) 2 zGlobal)))
    have hActualCanonicalPointCoordinate (q : E) :
        Φ q (homologyToRelative E ({q}ᶜ) 2 zGlobal) =
        kPoint q • CircleFundamentalCycle.fundamentalClass := by
      apply CircleHomologyComputation.circleH1Iso.toLinearEquiv.injective
      change CircleHomologyComputation.circleH1Iso.hom
        (Φ q (homologyToRelative E ({q}ᶜ) 2 zGlobal)) =
        CircleHomologyComputation.circleH1Iso.hom (kPoint q • CircleFundamentalCycle.fundamentalClass)
      rw [map_zsmul,CircleFundamentalCycle.fundamentalClass_coordinate]
      change CircleHomologyComputation.circleH1Iso.hom
        (Φ q (homologyToRelative E ({q}ᶜ) 2 zGlobal)) =
        (-(CircleHomologyComputation.circleH1Iso.hom
          (Φ q (homologyToRelative E ({q}ᶜ) 2 zGlobal)))) * (-1:ℤ)
      ring
    have hActualCanonicalPointCoordinateNonzero (q : E) : kPoint q ≠ 0 := by
      intro hk
      have hcoord := hActualCanonicalPointCoordinate q
      rw [hk,zero_smul] at hcoord
      apply hActualGlobalLocalizationsNonzero q
      haveI : IsIso (Φ q) := hΦiso q
      apply (ModuleCat.mono_iff_injective (Φ q)).mp inferInstance
      rw [map_zero]
      exact hcoord
    have hActualSingleDiscCoefficientPropagation
        (p : E) (ρ : ℝ) (hρ : 0 < ρ)
        (htarget : closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target)
        (t : relativeHomology E
          (((chartAt ℂ p).symm '' ball ((chartAt ℂ p) p) ρ)ᶜ) 2)
        (hpositive : ∀ q ∈ (chartAt ℂ p).symm '' ball ((chartAt ℂ p) p) ρ,
          ∀ havoid : ∀ x ∈ (((chartAt ℂ p).symm '' ball ((chartAt ℂ p) p) ρ)ᶜ), x ≠ q,
          Φ q (pairRelativeHomologyMap
            (((chartAt ℂ p).symm '' ball ((chartAt ℂ p) p) ρ)ᶜ)
            ({q}ᶜ) (ContinuousMap.id E) havoid 2 t) =
            CircleFundamentalCycle.fundamentalClass) :
        ∀ q ∈ (chartAt ℂ p).symm '' ball ((chartAt ℂ p) p) ρ,
          kPoint q = kPoint p := by
      let U := (chartAt ℂ p).symm '' ball ((chartAt ℂ p) p) ρ
      let Q : Set E := Uᶜ
      have hpU : p ∈ U := ⟨(chartAt ℂ p) p,mem_ball_self hρ,
        (chartAt ℂ p).left_inv (mem_chart_source ℂ p)⟩
      have hsingleton : ∃ havoid : ∀ x ∈ Q, x ≠ p,
          Function.Injective (pairRelativeHomologyMap Q ({p}ᶜ)
            (ContinuousMap.id E) havoid 2) := by
        run_tac do
          let n := Lean.Name.str (Lean.Name.num
            (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str .anonymous "_private") "CurveComplexGenusTwo") "Topology") "ActualMorseEulerExports") "SingletonRelativeDetection") 0)
            "actual_literal_chart_disc_exterior_point_detection"
          Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) _ _ _ (by assumption) (by assumption)))
      obtain ⟨havoidp,hinj⟩ := hsingleton
      have hnat (q : E) (havoid : ∀ x ∈ Q, x ≠ q) :
          pairRelativeHomologyMap Q ({q}ᶜ) (ContinuousMap.id E) havoid 2
            (homologyToRelative E Q 2 zGlobal) = homologyToRelative E ({q}ᶜ) 2 zGlobal := by
        have hn := pairRelativeHomologyMap_commutes Q ({q}ᶜ)
          (ContinuousMap.id E) havoid 2
        have hid : HomologicalComplex.homologyMap
            ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
              (ModuleCat.of ℤ ℤ)).map) (TopCat.ofHom (ContinuousMap.id E))) 2 =
            CategoryTheory.CategoryStruct.id (H E 2) := by
          change HomologicalComplex.homologyMap
            ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
              (ModuleCat.of ℤ ℤ)).map) (CategoryTheory.CategoryStruct.id (TopCat.of E))) 2 = _
          simp
          rfl
        rw [hid] at hn
        exact congrArg (fun f => f zGlobal) hn
      have hclass : homologyToRelative E Q 2 zGlobal = kPoint p • t := by
        apply hinj
        haveI : IsIso (Φ p) := hΦiso p
        apply (ModuleCat.mono_iff_injective (Φ p)).mp inferInstance
        rw [map_zsmul,map_zsmul,hpositive p hpU havoidp,hnat]
        exact hActualCanonicalPointCoordinate p
      intro q hq
      let havoidq : ∀ x ∈ Q, x ≠ q := fun x hx he => hx (he ▸ hq)
      have hc := congrArg (fun a => Φ q
        (pairRelativeHomologyMap Q ({q}ᶜ) (ContinuousMap.id E) havoidq 2 a)) hclass
      rw [map_zsmul,map_zsmul,hpositive q hq havoidq,hnat,
        hActualCanonicalPointCoordinate] at hc
      have he := congrArg CircleHomologyComputation.circleH1Iso.hom hc
      simp only [map_zsmul] at he
      change kPoint q * CircleHomologyComputation.circleH1Iso.hom
        CircleFundamentalCycle.fundamentalClass = kPoint p *
        CircleHomologyComputation.circleH1Iso.hom CircleFundamentalCycle.fundamentalClass at he
      rw [CircleFundamentalCycle.fundamentalClass_coordinate] at he
      omega
    have hActualGlobalCoefficientConstantOnLiteralDisc
        (p : E) (ρ : ℝ) (hρ : 0 < ρ)
        (htarget : closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
        ∀ q ∈ (chartAt ℂ p).symm '' ball ((chartAt ℂ p) p) ρ,
          kPoint q = kPoint p := by
      let c := chartAt ℂ p
      let D := closedBall (c p) ρ
      let B : Set D := {x | dist x.val (c p) = ρ}
      let U := c.symm '' ball (c p) ρ
      let Q : Set E := Uᶜ
      obtain ⟨γ,hγ,rD,hrD⟩ := actual_literal_complex_closed_disc_relative_cap_class (c p) ρ hρ
      let m : C(D,E) := ⟨fun x => c.symm x.val,
        c.symm.continuousOn.comp_continuous continuous_subtype_val (fun x => htarget x.property)⟩
      have hpair : ∀ x ∈ B, m x ∈ Q := by
        intro x hx hU
        obtain ⟨w,hw,he⟩ := hU
        have hwtarget : w ∈ c.target := htarget (ball_subset_closedBall hw)
        have hxtarget : x.val ∈ c.target := htarget x.property
        have heq : w = x.val := by
          have hh := congrArg c he
          change c (c.symm w) = c (c.symm x.val) at hh
          rw [c.right_inv hwtarget,c.right_inv hxtarget] at hh
          exact hh
        have hxB : dist x.val (c p) = ρ := hx
        rw [heq,mem_ball,hxB] at hw
        exact (lt_irrefl ρ) hw
      let t := pairRelativeHomologyMap B Q m hpair 2 rD
      apply hActualSingleDiscCoefficientPropagation p ρ hρ htarget t
      intro q hq havoid
      obtain ⟨w,hw,he⟩ := hq
      have hwt : w ∈ c.target := htarget (ball_subset_closedBall hw)
      have hqsource : q ∈ c.source := he ▸ c.map_target hwt
      have hcq : c q = w := by rw [← he,c.right_inv hwt]
      obtain ⟨hB,hpos⟩ := hΦallLiteralCaps p ρ hρ htarget γ hγ rD hrD m
        (fun x => rfl) q hqsource (by change dist (c q) (c p) < ρ; rw [hcq]; exact mem_ball.mp hw)
      have hn := pairRelativeHomologyMap_comp B Q ({q}ᶜ) m
        (ContinuousMap.id E) hpair havoid 2
      have heq := congrArg (fun f => f rD) hn
      change pairRelativeHomologyMap B ({q}ᶜ) m hB 2 rD =
        pairRelativeHomologyMap Q ({q}ᶜ) (ContinuousMap.id E) havoid 2 t at heq
      rw [← heq]
      exact hpos
    have hActualGlobalCoefficientLocallyConstant : IsLocallyConstant kPoint := by
      apply (IsLocallyConstant.iff_exists_open kPoint).mpr
      intro p
      let c := chartAt ℂ p
      obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp c.open_target (c p)
        (c.map_source (mem_chart_source ℂ p))
      let ρ := ε/2
      have hρ : 0 < ρ := half_pos hε
      have htarget : closedBall (c p) ρ ⊆ c.target := by
        intro w hw
        apply hball
        exact lt_of_le_of_lt (mem_closedBall.mp hw) (half_lt_self hε)
      let U := c.symm '' ball (c p) ρ
      refine ⟨U,c.isOpen_image_symm_of_subset_target isOpen_ball
        (fun x hx => htarget (ball_subset_closedBall hx)),?_,?_⟩
      · exact ⟨c p,mem_ball_self hρ,c.left_inv (mem_chart_source ℂ p)⟩
      · exact hActualGlobalCoefficientConstantOnLiteralDisc p ρ hρ htarget
    have hActualGlobalCoefficientCommon : ∃ k : ℤ, k ≠ 0 ∧ ∀ q, kPoint q = k := by
      let p : E := Classical.arbitrary E
      refine ⟨kPoint p,hActualCanonicalPointCoordinateNonzero p,?_⟩
      intro q
      exact hActualGlobalCoefficientLocallyConstant.apply_eq_of_preconnectedSpace q p
    obtain ⟨k,hk,hcommon⟩ := hActualGlobalCoefficientCommon
    refine ⟨zGlobal,Φ,k,hk,hΦiso,hActualGlobalLocalizationsNonzero,?_,hΦallLiteralCaps⟩
    intro q
    rw [← hcommon q]
    exact hActualCanonicalPointCoordinate q)

