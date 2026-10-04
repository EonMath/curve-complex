import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualGenusTwoCotangentDimensionTwoComplete85
import CurveComplexGenusTwo.Topology.ActualHaasUniqueness.ActualCanonicalPositiveZeroOrdersCanonical85
import CurveComplexGenusTwo.Topology.ActualHaasUniqueness.ActualCanonicalUniquenessReductionCanonical85
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.ActualHolomorphicInvolutionQuotientLiteralHolomorphicAtlas
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.ActualHolomorphicSixFixedInvolutionCompatibleBranchedDoubleCover
import actual_branch_coordinate_square_fiberPROVED
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import isolated_involution_strict_derivative_negativePROVED
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.HolomorphicInvolutionBiholomorphicBranchCoordinate
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Separation.Basic
import actual_local_negation_quotient_literal_square_chartPROVED
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.ActualInvolutionCompactHausdorffQuotient
import Mathlib.Topology.IsLocalHomeomorph
import actual_global_orientation_from_one_germPROVED
import chart_central_inversion_local_homology_identityPROVED
import actual_genus_two_complex_chart_orientation_sectionsPROVED
import negative_mobius_moving_center_local_top_homologyPROVED
import smooth_hyperbolic_chart_open_restrictionPROVED
import smooth_hyperbolic_chart_reflectionPROVED
import actual_hyperbolic_chart_complex_plane_modelPROVED
import positive_chart_coefficients_force_positive_mobius_transitionPROVED
import positive_hyperbolic_chart_family_complex_manifoldPROVED
import positive_mobius_germs_holomorphic_mapPROVED
import actual_genus_two_local_orientation_classPROVED
import ActualHyperbolicAxisAllPROVED
import ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Hyperbolic.Cayley
import CurveComplexGenusTwo.Topology.PositionExtension.SurfacePuncture
import CurveComplexGenusTwo.Topology.LocalOrientation.LocalReflectionGerm
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

set_option backward.isDefEq.respectTransparency false
namespace CurveComplex.Hyperbolic

open Matrix
open CategoryTheory CategoryTheory.Limits Topology
open CurveComplexGenusTwo.CWHurewicz
open CurveComplex.GenusOrientationCandidate
open scoped MatrixGroups Manifold ContDiff NNReal ComplexConjugate
open Set unitInterval Schoenflies

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

set_option maxHeartbeats 2000000 in
/-- Source uniqueness after the six-fixed-point gluing. The supplied metric
need not be globally intrinsic: the glued homeomorphism preserves distances
on a neighborhood of each point. The deck uses the original supplied isometry. -/
theorem actual_genus_two_six_fixed_local_isometry_unique
    (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E)
    (hdeck : letI : MetricSpace E := H.metric
      Isometry (M.cover.deck : E → E))
    (J : E ≃ₜ E)
    (hJ : ∀ x : E, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      letI : MetricSpace E := H.metric
      ∀ y ∈ U, ∀ z ∈ U, dist (J y) (J z) = dist y z)
    (hJinv : Function.Involutive J)
    (hfix : ∃ F : Finset E, (F : Set E) = {x : E | J x = x} ∧ F.card = 6) :
    J = M.cover.deck := by
  exact (set_option maxHeartbeats 8000000 in by
    classical
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    letI : T2Space E := (Classical.choice M.genusTwo.2.1).toT2Space
    have isolated_invariant_fixed_neighborhood :
        ∃ x : E, J x = x ∧ ∃ U : Set E,
          IsOpen U ∧ x ∈ U ∧ Set.MapsTo J U U ∧
            ∀ y ∈ U, J y = y ↔ y = x := by
      obtain ⟨F,hF,hcard⟩ := hfix
      have hne : F.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x,hx⟩ := hne
      have hxJ : J x = x := by
        have hh : x ∈ (F : Set E) := hx
        rw [hF] at hh
        exact hh
      let B : Set E := (F : Set E) \ {x}
      have hBfinite : B.Finite := F.finite_toSet.subset Set.sdiff_subset
      have hBclosed : IsClosed B := hBfinite.isClosed
      let V : Set E := Bᶜ
      have hxV : x ∈ V := by simp [V,B]
      let U : Set E := V ∩ J ⁻¹' V
      have hU : IsOpen U := hBclosed.isOpen_compl.inter
        (hBclosed.isOpen_compl.preimage J.continuous)
      have hxU : x ∈ U := ⟨hxV,by change J x ∈ V; rw [hxJ]; exact hxV⟩
      have hm : Set.MapsTo J U U := by
        intro y hy
        exact ⟨hy.2,by change J (J y) ∈ V; rw [hJinv y]; exact hy.1⟩
      refine ⟨x,hxJ,U,hU,hxU,hm,?_⟩
      intro y hy
      constructor
      · intro hyJ
        have hyF : y ∈ (F : Set E) := by rw [hF]; exact hyJ
        by_contra hne
        exact hy.1 ⟨hyF,by simpa only [Set.mem_singleton_iff] using hne⟩
      · intro hyx
        simpa only [hyx] using hxJ
    have chart_central_inversion_local_homology
        (S : Type) [TopologicalSpace S] [T2Space S]
        (x : S) (e : OpenPartialHomeomorph S (ℝ × ℝ))
        (hx : x ∈ e.source) (hex : e x = 0)
        (f : C(S,S))
        (hf : ∀ y ∈ ({x}ᶜ : Set S), f y ∈ ({x}ᶜ : Set S))
        (r : ℝ) (hr : 0 < r)
        (hball : Metric.closedBall (0 : ℝ × ℝ) r ⊆ e.target)
        (hgerm : ∀ z ∈ Metric.ball (0 : ℝ × ℝ) r,
          f (e.symm z) = e.symm (-z)) :
        pairRelativeHomologyMap ({x}ᶜ : Set S) ({x}ᶜ : Set S) f hf 2 =
          (𝟙 (relativeHomology S ({x}ᶜ : Set S) 2)) := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        let negation : C(ℝ × ℝ,ℝ × ℝ) := ⟨fun z => -z, continuous_neg⟩
        have hneg : ∀ z ∈ ({(0,0)}ᶜ : Set (ℝ × ℝ)), negation z ∈ ({(0,0)}ᶜ : Set (ℝ × ℝ)) := by
          intro z hz he
          apply hz
          change -z = (0,0) at he
          have hh := congrArg Neg.neg he
          simpa using hh
        have planeCentral : pairRelativeHomologyMap ({(0,0)}ᶜ : Set (ℝ × ℝ)) ({(0,0)}ᶜ : Set (ℝ × ℝ))
            negation hneg 2 = 𝟙 (relativeHomology (ℝ × ℝ) ({(0,0)}ᶜ : Set (ℝ × ℝ)) 2) := by
          let P : Set (ℝ × ℝ) := {(0,0)}ᶜ
          let q : C(ℝ × ℝ,ℝ × ℝ) := ⟨Prod.swap,continuous_swap⟩
          have hq : ∀ z ∈ P, q z ∈ P := by
            intro z hz hh
            apply hz
            change Prod.swap z = (0,0) at hh
            have he := congrArg Prod.swap hh
            exact he
          have hqq : q.comp q = ContinuousMap.id (ℝ × ℝ) := by ext z <;> rfl
          have hqqmap : pairRelativeHomologyMap P P q hq 2 ≫
              pairRelativeHomologyMap P P q hq 2 = 𝟙 (relativeHomology (ℝ × ℝ) P 2) := by
            rw [← pairRelativeHomologyMap_comp]
            exact (ReflectionGermProof.pairMap_congr P P (q.comp q) (ContinuousMap.id _)
              (fun z hz => hq (q z) (hq z hz)) (fun z hz => hz) hqq 2).trans
                (pairRelativeHomologyMap_id P 2)
          have hform : (⟨fun z : ℝ × ℝ => -z,continuous_neg⟩ : C(ℝ × ℝ,ℝ × ℝ)) =
              q.comp (planeReflection.comp (q.comp planeReflection)) := by
            ext z <;> rfl
          have hcomp : ∀ z ∈ P, (q.comp (planeReflection.comp (q.comp planeReflection))) z ∈ P := by
            intro z hz
            exact hq _ (planeReflection_preserves_puncture (q (planeReflection z)) (hq (planeReflection z) (planeReflection_preserves_puncture z hz)))
          have hf := ReflectionGermProof.pairMap_congr P P
            (⟨fun z : ℝ × ℝ => -z,continuous_neg⟩ : C(ℝ × ℝ,ℝ × ℝ))
              (q.comp (planeReflection.comp (q.comp planeReflection))) hneg hcomp hform 2
          rw [hf, pairRelativeHomologyMap_comp P P P _ q
            (fun z hz => planeReflection_preserves_puncture (q (planeReflection z)) (hq (planeReflection z) (planeReflection_preserves_puncture z hz))) hq,
            pairRelativeHomologyMap_comp P P P _ planeReflection
            (fun z hz => hq (planeReflection z) (planeReflection_preserves_puncture z hz)) planeReflection_preserves_puncture,
            pairRelativeHomologyMap_comp P P P planeReflection q planeReflection_preserves_puncture hq]
          rw [planeReflection_relativeHomologyMap_eq_neg_id]
          dsimp only [P] at hqqmap ⊢
          simpa only [Preadditive.neg_comp,Preadditive.comp_neg,Category.id_comp,
            Category.comp_id,neg_neg] using hqqmap
        let B : Set (ℝ × ℝ) := Metric.ball 0 r
        let W : Set S := e.source ∩ e ⁻¹' B
        have hB : B ⊆ e.target := fun z hz => hball (Metric.ball_subset_closedBall hz)
        have hW : IsOpen W := e.isOpen_inter_preimage Metric.isOpen_ball
        have hxW : x ∈ W := ⟨hx,by
          change e x ∈ Metric.ball 0 r
          simpa only [hex,Metric.mem_ball,dist_self] using hr⟩
        let c : B ≃ₜ W := {
          toFun := fun z => ⟨e.symm z,⟨e.map_target (hB z.property),by
            change e (e.symm z.val) ∈ B
            rw [e.right_inv (hB z.property)]
            exact z.property⟩⟩
          invFun := fun y => ⟨e y,y.property.2⟩
          left_inv := fun z => Subtype.ext (e.right_inv (hB z.property))
          right_inv := fun y => Subtype.ext (e.left_inv y.property.1)
          continuous_toFun := (e.symm.continuousOn.comp_continuous continuous_subtype_val
            (fun z => hB z.property)).subtype_mk _
          continuous_invFun := (e.continuousOn.comp_continuous continuous_subtype_val
            (fun y => y.property.1)).subtype_mk _ }
        let A : Set B := {z | z.val ≠ 0}
        let D : Set W := {y | y.val ≠ x}
        let C : Set S := {x}ᶜ
        let P : Set (ℝ × ℝ) := {0}ᶜ
        have hc : ∀ z ∈ A, c z ∈ D := by
          intro z hz he
          apply hz
          have hh := congrArg e he
          change e (e.symm z.val) = e x at hh
          rw [e.right_inv (hB z.property),hex] at hh
          exact hh
        have hci : ∀ y ∈ D, c.symm y ∈ A := by
          intro y hy he
          apply hy
          have he' : e y.val = e x := he.trans hex.symm
          exact e.injOn y.property.1 hx he'
        let k : C(B,W) := ⟨c,c.continuous⟩
        let i : C(B,S) := (ReflectionGermProof.inclusion W).comp k
        let j : C(B,ℝ × ℝ) := ReflectionGermProof.inclusion B
        have hi : ∀ z ∈ A, i z ∈ C := hc
        have hj : ∀ z ∈ A, j z ∈ P := fun z hz => hz
        have hreflectionB : ∀ z ∈ B, negation z ∈ B := by
          intro z hz
          simpa only [B,Metric.mem_ball,dist_zero_right,negation,ContinuousMap.coe_mk,
            norm_neg] using hz
        let g : C(B,B) := ⟨fun z => ⟨negation z,hreflectionB z.val z.property⟩,
          (negation.continuous.comp continuous_subtype_val).subtype_mk _⟩
        have hg : ∀ z ∈ A, g z ∈ A := by
          intro z hz
          exact hneg z.val hz
        have hiIso : IsIso (pairRelativeHomologyMap A C i hi 2) := by
          haveI hkIso : IsIso (pairRelativeHomologyMap A D k hc 2) :=
            ReflectionGermProof.pairHomeo_isIso A D c hc hci 2
          haveI hwIso : IsIso (pairRelativeHomologyMap D C (ReflectionGermProof.inclusion W)
              (fun y hy => hy) 2) := ReflectionGermProof.inclusion_isIso C W
            (ReflectionGermProof.puncture_excision x W hW hxW)
          have hm := pairRelativeHomologyMap_comp A D C k (ReflectionGermProof.inclusion W)
            hc (fun y hy => hy) 2
          rw [hm]
          infer_instance
        have hjIso : IsIso (pairRelativeHomologyMap A P j hj 2) :=
          ReflectionGermProof.inclusion_isIso P B
            (ReflectionGermProof.puncture_excision (0 : ℝ × ℝ) B Metric.isOpen_ball
              (by simpa only [B,Metric.mem_ball,dist_self] using hr))
        have hfg : f.comp i = i.comp g := by
          apply ContinuousMap.ext
          intro z
          change f (e.symm z.val) = e.symm (negation z.val)
          exact hgerm z.val z.property
        have hjg : negation.comp j = j.comp g := by ext z <;> rfl
        have hpr : pairRelativeHomologyMap P P negation hneg 2 =
            (𝟙 (relativeHomology (ℝ × ℝ) P 2)) := planeCentral
        have hgn : pairRelativeHomologyMap A A g hg 2 = (𝟙 (relativeHomology B A 2)) := by
          apply (cancel_mono (pairRelativeHomologyMap A P j hj 2)).1
          calc
            pairRelativeHomologyMap A A g hg 2 ≫ pairRelativeHomologyMap A P j hj 2 =
                pairRelativeHomologyMap A P (j.comp g) (fun z hz => hj (g z) (hg z hz)) 2 :=
              (pairRelativeHomologyMap_comp A A P g j hg hj 2).symm
            _ = pairRelativeHomologyMap A P (negation.comp j)
                (fun z hz => hneg (j z) (hj z hz)) 2 :=
              ReflectionGermProof.pairMap_congr A P _ _ _ _ hjg.symm 2
            _ = pairRelativeHomologyMap A P j hj 2 ≫
                pairRelativeHomologyMap P P negation hneg 2 :=
              pairRelativeHomologyMap_comp A P P j negation hj hneg 2
            _ = ((𝟙 (relativeHomology B A 2))) ≫ pairRelativeHomologyMap A P j hj 2 := by
              rw [hpr]
              simp only [Preadditive.comp_neg,Preadditive.neg_comp,Category.comp_id,Category.id_comp]
        apply (cancel_epi (pairRelativeHomologyMap A C i hi 2)).1
        calc
          pairRelativeHomologyMap A C i hi 2 ≫ pairRelativeHomologyMap C C f hf 2 =
              pairRelativeHomologyMap A C (f.comp i) (fun z hz => hf (i z) (hi z hz)) 2 :=
            (pairRelativeHomologyMap_comp A C C i f hi hf 2).symm
          _ = pairRelativeHomologyMap A C (i.comp g) (fun z hz => hi (g z) (hg z hz)) 2 :=
            ReflectionGermProof.pairMap_congr A C _ _ _ _ hfg 2
          _ = pairRelativeHomologyMap A A g hg 2 ≫ pairRelativeHomologyMap A C i hi 2 :=
            pairRelativeHomologyMap_comp A A C g i hg hi 2
          _ = pairRelativeHomologyMap A C i hi 2 ≫ ((𝟙 (relativeHomology S C 2))) := by
            rw [hgn]
            simp only [Preadditive.comp_neg,Preadditive.neg_comp,Category.comp_id,Category.id_comp]
      
      )
    have actual_genus_local_orientation_class (M : HyperellipticModel E S) :
        (∀ x : E, Mono (homologyToRelative E ({x}ᶜ : Set E) 2)) ∧
        ∃ z : integralHomology E 2, z ≠ 0 ∧
          ∀ x : E, homologyToRelative E ({x}ᶜ : Set E) 2 z ≠ 0 := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        classical
        letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
        have hmono (x : E) : Mono (homologyToRelative E ({x}ᶜ : Set E) 2) := by
          obtain ⟨hz,hexact⟩ := pairHomology_exact_at_absolute E ({x}ᶜ : Set E) 2
          apply hexact.mono_g
          exact CurveComplex.GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x
        obtain ⟨e⟩ := M.genusTwo.2.2.1
        let z : integralHomology E 2 := e.inv (1 : ℤ)
        have hz : z ≠ 0 := by
          intro hz
          have hi := e.inv_hom_id_apply (1 : ℤ)
          change e.hom z = 1 at hi
          rw [hz] at hi
          simpa using hi
        refine ⟨hmono,z,hz,?_⟩
        intro x hx
        letI := hmono x
        apply hz
        apply (ModuleCat.mono_iff_injective (homologyToRelative E ({x}ᶜ : Set E) 2)).mp inferInstance
        change (homologyToRelative E ({x}ᶜ : Set E) 2).hom z =
          (homologyToRelative E ({x}ᶜ : Set E) 2).hom 0
        rw [map_zero]
        exact hx
      )
    have actual_orientation_class_transport (z : integralHomology E 2) (x : E) :
        ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
          ∃ e : E ≃ₜ E, e x = y ∧
            ∃ hpres : ∀ t ∈ ({x}ᶜ : Set E), e t ∈ ({y}ᶜ : Set E),
              pairRelativeHomologyMap ({x}ᶜ : Set E) ({y}ᶜ : Set E)
                ⟨e,e.continuous⟩ hpres 2
                  (homologyToRelative E ({x}ᶜ : Set E) 2 z) =
                    homologyToRelative E ({y}ᶜ : Set E) 2 z := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        obtain ⟨U,hU,hxU,hmove⟩ := CurveComplex.GenusOrientationCandidate.surface_point_move_local E x
        refine ⟨U,hU,hxU,?_⟩
        intro y hy
        obtain ⟨G,hG⟩ := hmove y hy
        obtain ⟨e,he⟩ := G.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
        have hex : e x = y := (he x).trans hG
        let f : C(E,E) := ⟨e,e.continuous⟩
        let Hf : ContinuousMap.Homotopy (ContinuousMap.id E) f := {
          toContinuousMap := G.map
          map_zero_left := G.at_zero
          map_one_left := fun t => (he t).symm }
        have hpres : ∀ t ∈ ({x}ᶜ : Set E), e t ∈ ({y}ᶜ : Set E) := by
          intro t ht
          change t ≠ x at ht
          change e t ≠ y
          intro hh
          exact ht (e.injective (hh.trans hex.symm))
        refine ⟨e,hex,hpres,?_⟩
        have hn := pairRelativeHomologyMap_commutes
          ({x}ᶜ : Set E) ({y}ᶜ : Set E) f hpres 2
        let Htop : TopCat.Homotopy (TopCat.ofHom (ContinuousMap.id E)) (TopCat.ofHom f) := Hf
        have hh := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          Htop (ModuleCat.of ℤ ℤ) 2
        change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (ContinuousMap.id E))) =
            (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) at hh
        have hid : HomologicalComplex.homologyMap
            (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
              (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) 2 = 𝟙 (integralHomology E 2) := by
          change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) = _
          rw [← hh]
          exact CategoryTheory.Functor.map_id _ _
        rw [hid] at hn
        have hp := congrArg (fun q : integralHomology E 2 ⟶ relativeHomology E ({y}ᶜ : Set E) 2 => q z) hn
        change pairRelativeHomologyMap ({x}ᶜ : Set E) ({y}ᶜ : Set E) f hpres 2
          (homologyToRelative E ({x}ᶜ : Set E) 2 z) = homologyToRelative E ({y}ᶜ : Set E) 2 z at hp
        exact hp
      )
    have actual_global_orientation_from_one_germ (M : HyperellipticModel E S) (f : E ≃ₜ E) (x : E)
        (hpres : ∀ y ∈ ({x}ᶜ : Set E), f y ∈ ({x}ᶜ : Set E))
        (hlocal : pairRelativeHomologyMap ({x}ᶜ : Set E) ({x}ᶜ : Set E)
          ⟨f,f.continuous⟩ hpres 2 = 𝟙 (relativeHomology E ({x}ᶜ : Set E) 2)) :
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (⟨f,f.continuous⟩ : C(E,E)))) =
            𝟙 (integralHomology E 2) := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
        have hmono : Mono (homologyToRelative E ({x}ᶜ : Set E) 2) := by
          obtain ⟨hz,hexact⟩ := pairHomology_exact_at_absolute E ({x}ᶜ : Set E) 2
          apply hexact.mono_g
          exact CurveComplex.GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x
        letI := hmono
        have hn := pairRelativeHomologyMap_commutes
          ({x}ᶜ : Set E) ({x}ᶜ : Set E) (⟨f,f.continuous⟩ : C(E,E)) hpres 2
        rw [hlocal,Category.comp_id] at hn
        apply (cancel_mono (homologyToRelative E ({x}ᶜ : Set E) 2)).1
        exact hn.symm.trans (Category.id_comp (homologyToRelative E ({x}ᶜ : Set E) 2)).symm
      )
    have actual_global_orientation_from_half_turn_chart
        (f : E ≃ₜ E) (x : E) (e : OpenPartialHomeomorph E (ℝ × ℝ))
        (hx : x ∈ e.source) (hex : e x = 0)
        (hf : ∀ y ∈ ({x}ᶜ : Set E), f y ∈ ({x}ᶜ : Set E))
        (r : ℝ) (hr : 0 < r)
        (hball : Metric.closedBall (0 : ℝ × ℝ) r ⊆ e.target)
        (hgerm : ∀ z ∈ Metric.ball (0 : ℝ × ℝ) r,
          f (e.symm z) = e.symm (-z)) :
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (⟨f,f.continuous⟩ : C(E,E)))) =
            𝟙 (integralHomology E 2) := by
      exact actual_global_orientation_from_one_germ M f x hf
        (chart_central_inversion_local_homology E x e hx hex ⟨f,f.continuous⟩ hf
          r hr hball hgerm)
    obtain ⟨actual_localization_mono,orientation_class,orientation_class_ne,
      orientation_class_local_ne⟩ := actual_genus_local_orientation_class M
    have actual_global_orientation_class_coherence :=
      actual_orientation_class_transport orientation_class
    letI : MetricSpace E := H.metric
    have local_chart_model (x : E) :
        ∃ (c d : SmoothHyperbolicChart E),
          x ∈ c.chart.source ∧ J x ∈ d.chart.source ∧
          ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
            ∃ hc : U ⊆ c.chart.source,
            ∃ hd : Set.MapsTo J U d.chart.source,
            ∀ y z : U,
              dist (⟨c.chart y.val, c.upper y.val (hc y.property)⟩ : UpperHalfPlane)
                  (⟨c.chart z.val, c.upper z.val (hc z.property)⟩ : UpperHalfPlane) =
                dist (⟨d.chart (J y.val), d.upper (J y.val) (hd y.property)⟩ : UpperHalfPlane)
                  (⟨d.chart (J z.val), d.upper (J z.val) (hd z.property)⟩ : UpperHalfPlane) := by
      obtain ⟨c, hxc⟩ := H.smooth_hyperbolic x
      obtain ⟨d, hJxd⟩ := H.smooth_hyperbolic (J x)
      obtain ⟨V, hV, hxV, hdist⟩ := hJ x
      let U : Set E := (V ∩ c.chart.source) ∩ J ⁻¹' d.chart.source
      have hU : IsOpen U :=
        (hV.inter c.chart.toOpenPartialHomeomorph.open_source).inter
          (d.chart.toOpenPartialHomeomorph.open_source.preimage J.continuous)
      have hxU : x ∈ U := ⟨⟨hxV,hxc⟩,hJxd⟩
      have hc : U ⊆ c.chart.source := fun _ hy => hy.1.2
      have hd : Set.MapsTo J U d.chart.source := fun _ hy => hy.2
      refine ⟨c,d,hxc,hJxd,U,hU,hxU,hc,hd,?_⟩
      intro y z
      rw [← c.metric_preserving ⟨y.val,hc y.property⟩ ⟨z.val,hc z.property⟩,
        ← d.metric_preserving ⟨J y.val,hd y.property⟩ ⟨J z.val,hd z.property⟩]
      exact (hdist y.val y.property.1.1 z.val z.property.1.1).symm
    have hyperbolic_reference_point_rigidity : ∀ (t s : ℝ) (ht : t ≠ 0) (hs : 0 < s) (hs1 : s ≠ 1)
      (z w : UpperHalfPlane)
      (hA : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
      (hB : dist z (⟨⟨t,1⟩,by norm_num⟩ : UpperHalfPlane) =
        dist w (⟨⟨t,1⟩,by norm_num⟩ : UpperHalfPlane))
      (hC : dist z (⟨⟨0,s⟩,hs⟩ : UpperHalfPlane) =
        dist w (⟨⟨0,s⟩,hs⟩ : UpperHalfPlane)), z = w := by
      intro t s ht hs hs1 z w hA hB hC  
      have hz : z.im ≠ 0 := ne_of_gt z.im_pos
      have hw : w.im ≠ 0 := ne_of_gt w.im_pos
      have h1 := congrArg Real.cosh hA
      have h2 := congrArg Real.cosh hB
      have h3 := congrArg Real.cosh hC
      simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.I_re,
        UpperHalfPlane.I_im, sub_zero, one_pow, mul_one] at h1
      simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
        UpperHalfPlane.mk_im, one_pow, mul_one] at h2
      simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
        UpperHalfPlane.mk_im, sub_zero] at h3
      have H1 : (z.re ^ 2 + z.im ^ 2 + 1) * w.im =
          (w.re ^ 2 + w.im ^ 2 + 1) * z.im := by
        field_simp at h1
        nlinarith [h1]
      have H2 : ((z.re - t) ^ 2 + z.im ^ 2 + 1) * w.im =
          ((w.re - t) ^ 2 + w.im ^ 2 + 1) * z.im := by
        field_simp at h2
        nlinarith [h2]
      have H3 : (z.re ^ 2 + z.im ^ 2 + s ^ 2) * w.im =
          (w.re ^ 2 + w.im ^ 2 + s ^ 2) * z.im := by
        field_simp at h3
        nlinarith [h3]
      have hs2 : s ^ 2 - 1 ≠ 0 := by
        have hm : (s - 1) * (s + 1) ≠ 0 :=
          mul_ne_zero (sub_ne_zero.mpr hs1) (by linarith)
        intro h
        apply hm
        nlinarith [h]
      have hp : (s ^ 2 - 1) * (w.im - z.im) = 0 := by
        nlinarith [H1,H3]
      have him : z.im = w.im := by
        have he := (mul_eq_zero.mp hp).resolve_left hs2
        linarith
      have hp' : t * (z.re - w.re) * z.im = 0 := by
        rw [← him] at H1 H2
        nlinarith [H1,H2]
      have hre : z.re = w.re := by
        have he := (mul_eq_zero.mp hp').resolve_right hz
        have he' := (mul_eq_zero.mp he).resolve_left ht
        linarith
      apply UpperHalfPlane.ext
      exact Complex.ext hre him
    have normalize_at_arbitrary_radius : ∀ (r : ℝ) (hr : 0 < r) (z : H2)
      (h : dist UpperHalfPlane.I z = r),
      ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = UpperHalfPlane.I ∧
        e (verticalPath r) = z := by
      intro r hr z h  
      have hzero : verticalPath 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
      have hstd : dist UpperHalfPlane.I (verticalPath r) = r := by
        rw [← hzero,verticalPath_isometry.dist_eq]
        simp [Real.dist_eq,abs_of_pos hr]
      have hsphere : Real.exp r * (z.re ^ 2 + z.im ^ 2 + 1) =
          z.im * (1 + (Real.exp r) ^ 2) := by
        have hc := congrArg Real.cosh (h.trans hstd.symm)
        rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
        simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,
          UpperHalfPlane.I_re,UpperHalfPlane.I_im,zero_sub,neg_sq,one_pow,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hc
        field_simp at hc
        nlinarith [hc]
      let a : ℝ := 1 - Real.exp r * z.im
      let b : ℝ := z.re
      by_cases hpole : a = 0 ∧ b = 0
      · have him : z.im = Real.exp (-r) := by
          have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
          have ha : Real.exp r * z.im = 1 := by dsimp [a] at hpole; linarith [hpole.1]
          rw [Real.exp_neg,← one_div]
          exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
        have hz : z = verticalPath (-r) := by
          apply UpperHalfPlane.ext_re_im
          · simpa [verticalPath,b] using hpole.2
          · simpa [verticalPath] using him
        refine ⟨IsometryEquiv.constSMul
          (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S),?_,?_⟩
        · rw [← hzero]
          change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath 0
          have hh := modular_S_verticalPath 0
          change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath (-0) at hh
          simpa only [neg_zero] using hh
        · rw [hz]
          change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath r : H2) = verticalPath (-r)
          exact modular_S_verticalPath r
      · have hab : 0 < a ^ 2 + b ^ 2 := by
          by_contra hn
          have ha : a = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
          have hb : b = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
          exact hpole ⟨ha,hb⟩
        refine ⟨IsometryEquiv.constSMul (stabilizerRotation a b hab),
          stabilizerRotation_fixes_I a b hab,?_⟩
        change (stabilizerRotation a b hab • verticalPath r : H2) = z
        have hden (w : H2) : (-(b : ℂ) * (w : ℂ) + a) ≠ 0 := by
          intro he
          have him := congrArg Complex.im he
          simp [Complex.mul_im] at him
          have hb : b = 0 := by
            rcases him with hb | hw
            · exact hb
            · exact (w.im_pos.ne' hw).elim
          have ha : a ≠ 0 := by
            intro ha
            rw [ha,hb] at hab
            norm_num at hab
          exact ha (by simpa [hb] using he)
        have hEim : (Complex.exp (r : ℂ)).im = 0 := Complex.exp_ofReal_im r
        have hEre : (Complex.exp (r : ℂ)).re = Real.exp r := Complex.exp_ofReal_re r
        apply UpperHalfPlane.coe_injective
        rw [stabilizerRotation_coe_smul]
        apply (div_eq_iff (hden (verticalPath r))).2
        apply Complex.ext
        · simp [verticalPath,Complex.add_re,Complex.mul_re,Complex.neg_re,
            Complex.mul_im,Complex.neg_im]
          dsimp [a,b]
          ring
        · simp [verticalPath,Complex.add_im,Complex.mul_im,Complex.neg_im,
            Complex.mul_re,Complex.neg_re]
          dsimp [a,b]
          nlinarith [hsphere]
    have ordered_pair_at_arbitrary_distance (r : ℝ) (hr : 0 < r)
        (a b : H2) (hd : dist a b = r) :
        ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = a ∧ e (verticalPath r) = b := by
      let e₀ : H2 ≃ᵢ H2 := IsometryEquiv.constSMul a.toSL2R
      have h₀ : e₀ UpperHalfPlane.I = a := a.toSL2R_smul_I
      let w : H2 := e₀.symm b
      have hw : dist UpperHalfPlane.I w = r := by
        have he := e₀.dist_eq UpperHalfPlane.I (e₀.symm b)
        rw [e₀.apply_symm_apply,h₀] at he
        exact he.symm.trans hd
      obtain ⟨q,hqI,hqr⟩ := normalize_at_arbitrary_radius r hr w hw
      refine ⟨q.trans e₀,?_,?_⟩
      · rw [IsometryEquiv.trans_apply,hqI,h₀]
      · rw [IsometryEquiv.trans_apply,hqr]
        exact e₀.apply_symm_apply b
    have local_plane_extension (U : Set H2) (hU : IsOpen U) (hne : U.Nonempty)
        (f : U → H2) (hf : Isometry f) :
        ∃ e : H2 ≃ᵢ H2, ∀ z : U, e z.val = f z := by
      have normalized_extension : ∀ (t r : ℝ) (ht : t ≠ 0) (hr : 0 < r)
        (U : Set H2) (hA : UpperHalfPlane.I ∈ U)
        (hB : (⟨⟨t,1⟩,by norm_num⟩ : H2) ∈ U) (hC : verticalPath r ∈ U)
        (f : U → H2) (hf : Isometry f),
        ∃ e : H2 ≃ᵢ H2, ∀ z : U, e z.val = f z := by
        intro t r ht hr U hA hB hC f hf
        classical
        have two_reference_ambiguity (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
            (z w : H2)
            (hA : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
            (hC : dist z (⟨⟨0,s⟩,hs⟩ : H2) = dist w (⟨⟨0,s⟩,hs⟩ : H2)) :
            z.im = w.im ∧ (z.re = w.re ∨ z.re = -w.re) := by
          have hz : z.im ≠ 0 := ne_of_gt z.im_pos
          have hw : w.im ≠ 0 := ne_of_gt w.im_pos
          have h1 := congrArg Real.cosh hA
          have h3 := congrArg Real.cosh hC
          simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.I_re,
            UpperHalfPlane.I_im, sub_zero, one_pow, mul_one] at h1
          simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
            UpperHalfPlane.mk_im, sub_zero] at h3
          have H1 : (z.re ^ 2 + z.im ^ 2 + 1) * w.im =
              (w.re ^ 2 + w.im ^ 2 + 1) * z.im := by
            field_simp at h1
            nlinarith [h1]
          have H3 : (z.re ^ 2 + z.im ^ 2 + s ^ 2) * w.im =
              (w.re ^ 2 + w.im ^ 2 + s ^ 2) * z.im := by
            field_simp at h3
            nlinarith [h3]
          have hs2 : s ^ 2 - 1 ≠ 0 := by
            have hm : (s - 1) * (s + 1) ≠ 0 :=
              mul_ne_zero (sub_ne_zero.mpr hs1) (by linarith)
            intro h
            apply hm
            nlinarith [h]
          have hp : (s ^ 2 - 1) * (w.im - z.im) = 0 := by
            nlinarith [H1,H3]
          have him : z.im = w.im := by
            have he := (mul_eq_zero.mp hp).resolve_left hs2
            linarith
          have hsq : z.re ^ 2 = w.re ^ 2 := by
            rw [← him] at H1
            have he : (z.re ^ 2 - w.re ^ 2) * z.im = 0 := by nlinarith [H1]
            have he' := (mul_eq_zero.mp he).resolve_right hz
            linarith
          exact ⟨him,sq_eq_sq_iff_eq_or_eq_neg.mp hsq⟩
        let R : H2 ≃ᵢ H2 := {
          toFun := fun z => ⟨⟨-z.re,z.im⟩,z.im_pos⟩
          invFun := fun z => ⟨⟨-z.re,z.im⟩,z.im_pos⟩
          left_inv := by intro z; apply UpperHalfPlane.ext_re_im <;> simp
          right_inv := by intro z; apply UpperHalfPlane.ext_re_im <;> simp
          isometry_toFun := Isometry.of_dist_eq (by
            intro z w
            apply Real.cosh_strictMonoOn.injOn (dist_nonneg) (dist_nonneg)
            rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist']
            simp only [UpperHalfPlane.mk_re,UpperHalfPlane.mk_im]
            congr 1
            ring) }
        have hRI : R UpperHalfPlane.I = UpperHalfPlane.I := by
          apply UpperHalfPlane.ext_re_im <;> simp [R]
        have hRC : R (verticalPath r) = verticalPath r := by
          apply UpperHalfPlane.ext_re_im <;> simp [R,verticalPath]
        let A : U := ⟨UpperHalfPlane.I,hA⟩
        let B : U := ⟨⟨⟨t,1⟩,by norm_num⟩,hB⟩
        let C : U := ⟨verticalPath r,hC⟩
        have hdAC : dist (f A) (f C) = r := by
          rw [hf.dist_eq]
          change dist UpperHalfPlane.I (verticalPath r) = r
          have hzero : verticalPath 0 = UpperHalfPlane.I := by
            apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
          rw [← hzero,verticalPath_isometry.dist_eq]
          simp [Real.dist_eq,abs_of_pos hr]
        obtain ⟨e₀,h₀A,h₀C⟩ := ordered_pair_at_arbitrary_distance r hr (f A) (f C) hdAC
        let g : U → H2 := fun z => e₀.symm (f z)
        have hg : Isometry g := e₀.symm.isometry.comp hf
        have hgA : g A = UpperHalfPlane.I := by
          dsimp [g]
          rw [← h₀A,e₀.symm_apply_apply]
        have hgC : g C = verticalPath r := by
          dsimp [g]
          rw [← h₀C,e₀.symm_apply_apply]
        have hBA : dist (g B) UpperHalfPlane.I = dist B.val UpperHalfPlane.I := by
          have hh := hg.dist_eq B A
          simpa only [hgA,Subtype.dist_eq,A] using hh
        have hBC : dist (g B) (verticalPath r) = dist B.val (verticalPath r) := by
          have hh := hg.dist_eq B C
          simpa only [hgC,Subtype.dist_eq,C] using hh
        have hs1 : Real.exp r ≠ 1 := by
          intro he
          have he' : r = 0 := Real.exp_injective (show Real.exp r = Real.exp 0 by simpa using he)
          linarith
        obtain ⟨him,hre⟩ := two_reference_ambiguity (Real.exp r) (Real.exp_pos r) hs1
          (g B) B.val hBA hBC
        have hBnormal : g B = B.val ∨ R (g B) = B.val := by
          rcases hre with hp | hn
          · left
            exact UpperHalfPlane.ext_re_im hp him
          · right
            apply UpperHalfPlane.ext_re_im
            · change -(g B).re = t
              change (g B).re = -t at hn
              linarith
            · exact him
        obtain ⟨q,hqA,hqB,hqC⟩ : ∃ q : H2 ≃ᵢ H2,
            q UpperHalfPlane.I = UpperHalfPlane.I ∧ q (g B) = B.val ∧
              q (verticalPath r) = verticalPath r := by
          rcases hBnormal with hp | hn
          · exact ⟨IsometryEquiv.refl _,rfl,hp,rfl⟩
          · exact ⟨R,hRI,hn,hRC⟩
        have hall (z : U) : q (g z) = z.val := by
          refine hyperbolic_reference_point_rigidity t (Real.exp r) ht (Real.exp_pos r) hs1 (q (g z)) z.val ?_ ?_ ?_
          · have hh := (q.isometry.comp hg).dist_eq z A
            simpa only [Function.comp_apply,hgA,hqA,Subtype.dist_eq,A] using hh
          · have hh := (q.isometry.comp hg).dist_eq z B
            simpa only [Function.comp_apply,hqB,Subtype.dist_eq] using hh
          · have hh := (q.isometry.comp hg).dist_eq z C
            change dist (q (g z)) (q (g C)) = dist z.val C.val at hh
            rw [hgC,hqC] at hh
            change dist (q (g z)) (verticalPath r) = dist z.val (verticalPath r) at hh
            simpa only [verticalPath] using hh
        refine ⟨q.symm.trans e₀,?_⟩
        intro z
        rw [IsometryEquiv.trans_apply,← hall z,q.symm_apply_apply]
        exact e₀.apply_symm_apply (f z)
      obtain ⟨p,hp⟩ := hne
      let a : H2 ≃ᵢ H2 := IsometryEquiv.constSMul p.toSL2R
      have ha : a UpperHalfPlane.I = p := p.toSL2R_smul_I
      let V : Set H2 := a ⁻¹' U
      have hV : IsOpen V := hU.preimage a.continuous
      have hIV : UpperHalfPlane.I ∈ V := by change a UpperHalfPlane.I ∈ U; rw [ha]; exact hp
      let horizontal : ℝ → H2 := fun t => ⟨⟨t,1⟩,by norm_num⟩
      have hhor : Continuous horizontal := by
        apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
        have hh : Continuous (fun t : ℝ => (t : ℂ) + Complex.I) :=
          Complex.continuous_ofReal.add continuous_const
        convert hh using 1
        ext t <;> simp [horizontal,Complex.ext_iff]
      have hhor0 : horizontal 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [horizontal]
      have hvert0 : verticalPath 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
      let W : Set ℝ := horizontal ⁻¹' V ∩ verticalPath ⁻¹' V
      have hW : IsOpen W :=
        (hV.preimage hhor).inter (hV.preimage verticalPath_isometry.continuous)
      have h0W : (0 : ℝ) ∈ W := by
        exact ⟨by change horizontal 0 ∈ V; rw [hhor0]; exact hIV,
          by change verticalPath 0 ∈ V; rw [hvert0]; exact hIV⟩
      obtain ⟨δ,hδ,hδW⟩ := Metric.isOpen_iff.mp hW 0 h0W
      let r := δ / 2
      have hr : 0 < r := by dsimp [r]; linarith
      have hrW : r ∈ W := hδW (by
        rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hr]
        dsimp [r]
        linarith)
      let F : V → H2 := fun z => f ⟨a z.val,z.property⟩
      have hF : Isometry F := Isometry.of_dist_eq (by
        intro z w
        calc
          dist (F z) (F w) = dist (a z.val) (a w.val) := hf.dist_eq _ _
          _ = dist z w := a.dist_eq _ _)
      obtain ⟨e,he⟩ := normalized_extension r r hr.ne' hr V hIV hrW.1 hrW.2 F hF
      refine ⟨a.symm.trans e,?_⟩
      intro z
      let y : V := ⟨a.symm z.val,by
        change a (a.symm z.val) ∈ U
        rw [a.apply_symm_apply]
        exact z.property⟩
      change e y.val = f z
      rw [he y]
      change f ⟨a (a.symm z.val),_⟩ = f z
      congr 1
      apply Subtype.ext
      exact a.apply_symm_apply z.val
    have local_chart_extension (x : E) :
        ∃ (c d : SmoothHyperbolicChart E),
          x ∈ c.chart.source ∧ J x ∈ d.chart.source ∧
          ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
            ∃ hc : U ⊆ c.chart.source,
            ∃ hd : Set.MapsTo J U d.chart.source,
            ∃ e : H2 ≃ᵢ H2, ∀ y : U,
              e (⟨c.chart y.val,c.upper y.val (hc y.property)⟩ : H2) =
                (⟨d.chart (J y.val),d.upper (J y.val) (hd y.property)⟩ : H2) := by
      obtain ⟨c,d,hxc,hJxd,U,hU,hxU,hc,hd,hmetric⟩ := local_chart_model x
      let V : Set H2 := {z | (z : ℂ) ∈ c.chart '' U}
      have hV : IsOpen V :=
        (c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU hc).preimage
          UpperHalfPlane.continuous_coe
      have hne : V.Nonempty :=
        ⟨⟨c.chart x,c.upper x (hc hxU)⟩,⟨x,hxU,rfl⟩⟩
      have hpreimage (z : V) : ∃ y : U, c.chart y.val = (z.val : ℂ) := by
        obtain ⟨y,hy,hcy⟩ := z.property
        exact ⟨⟨y,hy⟩,hcy⟩
      let lift : V → U := fun z => Classical.choose (hpreimage z)
      have hlift (z : V) : c.chart (lift z).val = (z.val : ℂ) :=
        Classical.choose_spec (hpreimage z)
      have hcoords (z : V) :
          (⟨c.chart (lift z).val,c.upper (lift z).val (hc (lift z).property)⟩ : H2) = z.val :=
        UpperHalfPlane.ext (hlift z)
      let F : V → H2 := fun z =>
        ⟨d.chart (J (lift z).val),d.upper (J (lift z).val) (hd (lift z).property)⟩
      have hF : Isometry F := Isometry.of_dist_eq (by
        intro y z
        change dist (⟨d.chart (J (lift y).val),_⟩ : H2)
          (⟨d.chart (J (lift z).val),_⟩ : H2) = dist y z
        rw [← hmetric (lift y) (lift z),hcoords y,hcoords z]
        rfl)
      obtain ⟨e,he⟩ := local_plane_extension V hV hne F hF
      refine ⟨c,d,hxc,hJxd,U,hU,hxU,hc,hd,e,?_⟩
      intro y
      let z : V := ⟨⟨c.chart y.val,c.upper y.val (hc y.property)⟩,
        ⟨y.val,y.property,rfl⟩⟩
      have hy : (lift z).val = y.val :=
        c.chart.toOpenPartialHomeomorph.injOn (hc (lift z).property) (hc y.property) (hlift z)
      change e z.val = (⟨d.chart (J y.val),_⟩ : H2)
      rw [he z]
      apply UpperHalfPlane.ext
      change d.chart (J (lift z).val) = d.chart (J y.val)
      rw [hy]
    have plane_extension_square_rigidity (U : Set H2) (hU : IsOpen U)
        (hne : U.Nonempty) (e : H2 ≃ᵢ H2)
        (hsquare : ∀ z ∈ U, e (e z) = z) : Function.Involutive e := by
      have open_agreement (U : Set H2) (hU : IsOpen U) (hne : U.Nonempty)
          (e d : H2 ≃ᵢ H2) (hagree : ∀ z ∈ U, e z = d z) : e = d := by
        have hyperbolic_reference_point_rigidity : ∀ (t s : ℝ) (ht : t ≠ 0) (hs : 0 < s) (hs1 : s ≠ 1)
          (z w : UpperHalfPlane)
          (hA : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
          (hB : dist z (⟨⟨t,1⟩,by norm_num⟩ : UpperHalfPlane) =
            dist w (⟨⟨t,1⟩,by norm_num⟩ : UpperHalfPlane))
          (hC : dist z (⟨⟨0,s⟩,hs⟩ : UpperHalfPlane) =
            dist w (⟨⟨0,s⟩,hs⟩ : UpperHalfPlane)), z = w := by
          intro t s ht hs hs1 z w hA hB hC  
          have hz : z.im ≠ 0 := ne_of_gt z.im_pos
          have hw : w.im ≠ 0 := ne_of_gt w.im_pos
          have h1 := congrArg Real.cosh hA
          have h2 := congrArg Real.cosh hB
          have h3 := congrArg Real.cosh hC
          simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.I_re,
            UpperHalfPlane.I_im, sub_zero, one_pow, mul_one] at h1
          simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
            UpperHalfPlane.mk_im, one_pow, mul_one] at h2
          simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
            UpperHalfPlane.mk_im, sub_zero] at h3
          have H1 : (z.re ^ 2 + z.im ^ 2 + 1) * w.im =
              (w.re ^ 2 + w.im ^ 2 + 1) * z.im := by
            field_simp at h1
            nlinarith [h1]
          have H2 : ((z.re - t) ^ 2 + z.im ^ 2 + 1) * w.im =
              ((w.re - t) ^ 2 + w.im ^ 2 + 1) * z.im := by
            field_simp at h2
            nlinarith [h2]
          have H3 : (z.re ^ 2 + z.im ^ 2 + s ^ 2) * w.im =
              (w.re ^ 2 + w.im ^ 2 + s ^ 2) * z.im := by
            field_simp at h3
            nlinarith [h3]
          have hs2 : s ^ 2 - 1 ≠ 0 := by
            have hm : (s - 1) * (s + 1) ≠ 0 :=
              mul_ne_zero (sub_ne_zero.mpr hs1) (by linarith)
            intro h
            apply hm
            nlinarith [h]
          have hp : (s ^ 2 - 1) * (w.im - z.im) = 0 := by
            nlinarith [H1,H3]
          have him : z.im = w.im := by
            have he := (mul_eq_zero.mp hp).resolve_left hs2
            linarith
          have hp' : t * (z.re - w.re) * z.im = 0 := by
            rw [← him] at H1 H2
            nlinarith [H1,H2]
          have hre : z.re = w.re := by
            have he := (mul_eq_zero.mp hp').resolve_right hz
            have he' := (mul_eq_zero.mp he).resolve_left ht
            linarith
          apply UpperHalfPlane.ext
          exact Complex.ext hre him
        obtain ⟨p,hp⟩ := hne
        let a : H2 ≃ᵢ H2 := IsometryEquiv.constSMul p.toSL2R
        have ha : a UpperHalfPlane.I = p := p.toSL2R_smul_I
        let V : Set H2 := a ⁻¹' U
        have hV : IsOpen V := hU.preimage a.continuous
        have hIV : UpperHalfPlane.I ∈ V := by change a UpperHalfPlane.I ∈ U; rw [ha]; exact hp
        let horizontal : ℝ → H2 := fun t => ⟨⟨t,1⟩,by norm_num⟩
        have hhor : Continuous horizontal := by
          apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
          have hh : Continuous (fun t : ℝ => (t : ℂ) + Complex.I) :=
            Complex.continuous_ofReal.add continuous_const
          convert hh using 1
          ext t <;> simp [horizontal,Complex.ext_iff]
        have hhor0 : horizontal 0 = UpperHalfPlane.I := by
          apply UpperHalfPlane.ext_re_im <;> simp [horizontal]
        have hvert0 : verticalPath 0 = UpperHalfPlane.I := by
          apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
        let W : Set ℝ := horizontal ⁻¹' V ∩ verticalPath ⁻¹' V
        have hW : IsOpen W :=
          (hV.preimage hhor).inter (hV.preimage verticalPath_isometry.continuous)
        have h0W : (0 : ℝ) ∈ W := by
          exact ⟨by change horizontal 0 ∈ V; rw [hhor0]; exact hIV,
            by change verticalPath 0 ∈ V; rw [hvert0]; exact hIV⟩
        obtain ⟨δ,hδ,hδW⟩ := Metric.isOpen_iff.mp hW 0 h0W
        let r := δ / 2
        have hr : 0 < r := by dsimp [r]; linarith
        have hrW : r ∈ W := hδW (by
          rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hr]
          dsimp [r]
          linarith)
        have heI : e (a UpperHalfPlane.I) = d (a UpperHalfPlane.I) := hagree _ hIV
        have heB : e (a (horizontal r)) = d (a (horizontal r)) := hagree _ hrW.1
        have heC : e (a (verticalPath r)) = d (a (verticalPath r)) := hagree _ hrW.2
        have hs1 : Real.exp r ≠ 1 := by
          intro h
          have hh : Real.exp r = Real.exp 0 := by simpa using h
          have := Real.exp_injective hh
          exact hr.ne' this
        apply IsometryEquiv.ext
        intro z
        have eqnorm : a.symm (e.symm (d z)) = a.symm z := by
          refine hyperbolic_reference_point_rigidity r (Real.exp r) hr.ne' (Real.exp_pos r) hs1 _ _ ?_ ?_ ?_
          · calc
              dist (a.symm (e.symm (d z))) UpperHalfPlane.I =
                  dist (d z) (e (a UpperHalfPlane.I)) := by
                    rw [← a.dist_eq, a.apply_symm_apply, ← e.dist_eq, e.apply_symm_apply]
              _ = dist (d z) (d (a UpperHalfPlane.I)) := by rw [heI]
              _ = dist (a.symm z) UpperHalfPlane.I := by
                rw [d.dist_eq]
                simpa only [a.symm_apply_apply] using (a.symm.dist_eq z (a UpperHalfPlane.I)).symm
          · change dist (a.symm (e.symm (d z))) (horizontal r) = dist (a.symm z) (horizontal r)
            calc
              dist (a.symm (e.symm (d z))) (horizontal r) = dist (d z) (e (a (horizontal r))) := by
                rw [← a.dist_eq, a.apply_symm_apply, ← e.dist_eq, e.apply_symm_apply]
              _ = dist (d z) (d (a (horizontal r))) := by rw [heB]
              _ = dist (a.symm z) (horizontal r) := by
                rw [d.dist_eq]
                simpa only [a.symm_apply_apply] using (a.symm.dist_eq z (a (horizontal r))).symm
          · change dist (a.symm (e.symm (d z))) (verticalPath r) = dist (a.symm z) (verticalPath r)
            calc
              dist (a.symm (e.symm (d z))) (verticalPath r) = dist (d z) (e (a (verticalPath r))) := by
                rw [← a.dist_eq, a.apply_symm_apply, ← e.dist_eq, e.apply_symm_apply]
              _ = dist (d z) (d (a (verticalPath r))) := by rw [heC]
              _ = dist (a.symm z) (verticalPath r) := by
                rw [d.dist_eq]
                simpa only [a.symm_apply_apply] using (a.symm.dist_eq z (a (verticalPath r))).symm
        have hz : e.symm (d z) = z := a.symm.injective eqnorm
        have hh := congrArg e hz
        simpa using hh.symm
      have he : e.trans e = IsometryEquiv.refl H2 :=
        open_agreement U hU hne (e.trans e) (IsometryEquiv.refl H2) hsquare
      intro z
      have hz := congrArg (fun f : H2 ≃ᵢ H2 => f z) he
      exact hz
    have actual_chart_isolated_fixed_mobius_orientation (J : E ≃ₜ E) (c : SmoothHyperbolicChart E)
        (x : E) (U : Set E) (hU : IsOpen U) (hxU : x ∈ U)
        (hc : U ⊆ c.chart.source) (hd : Set.MapsTo J U c.chart.source)
        (hx : J x = x) (hisolated : ∀ y ∈ U, J y = y → y = x)
        (g : GL (Fin 2) ℝ)
        (hcoord : ∀ y : U,
          g • (⟨c.chart y.val,c.upper y.val (hc y.property)⟩ : H2) =
            (⟨c.chart (J y.val),c.upper (J y.val) (hd y.property)⟩ : H2)) :
        0 < g.val.det ∧ MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) (fun z : H2 => g • z) := by
      have negative_not_isolated (g : GL (Fin 2) ℝ) (hneg : g.val.det < 0)
          (p : H2) (hp : g • p = p) (U : Set H2) (hU : IsOpen U) (hpU : p ∈ U) :
          ∃ z ∈ U, g • z = z ∧ z ≠ p := by
        have htrace : g.val.trace = 0 :=
          (UpperHalfPlane.exists_gl_smul_eq_self_iff_trace_eq_zero hneg).mp ⟨_,hp⟩
        by_cases hc : g 1 0 = 0
        · have hpr : p.re = g 0 1 / (2 * g 1 1) :=
            (UpperHalfPlane.gl_smul_eq_self_iff_re_eq htrace hc).mp hp
          let γ : ℝ → H2 := fun t => ⟨⟨p.re,p.im * Real.exp t⟩,
            mul_pos p.im_pos (Real.exp_pos t)⟩
          have hγ : Continuous γ := by
            apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
            have hh : Continuous (fun t : ℝ => (p.re : ℂ) +
                (p.im * Real.exp t : ℂ) * Complex.I) := by fun_prop
            convert hh using 1
            ext t <;> simp [γ,Complex.ext_iff,Complex.exp_ofReal_re,Complex.exp_ofReal_im]
          have hγ0 : γ 0 = p := by
            apply UpperHalfPlane.ext_re_im <;> simp [γ]
          have hW : IsOpen (γ ⁻¹' U) := hU.preimage hγ
          have h0 : (0 : ℝ) ∈ γ ⁻¹' U := by
            simpa only [Set.mem_preimage,hγ0] using hpU
          obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp hW 0 h0
          let t := δ / 2
          have ht : 0 < t := by dsimp [t]; linarith
          have htU : γ t ∈ U := hδU (by
            rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
            dsimp [t]; linarith)
          refine ⟨γ t,htU,?_,?_⟩
          · rw [UpperHalfPlane.gl_smul_eq_self_iff_re_eq htrace hc]
            exact hpr
          · intro hz
            have him := congrArg UpperHalfPlane.im hz
            change p.im * Real.exp t = p.im at him
            have he : Real.exp t = Real.exp 0 := by
              rw [Real.exp_zero]
              nlinarith [p.im_pos]
            exact ht.ne' (Real.exp_injective he)
        · let k : ℝ := -g 1 1 / g 1 0
          let P : ℝ → ℝ := fun t => p.im ^ 2 + 2 * (k-p.re) * t - t ^ 2
          let γ : ℝ → ℂ := fun t => ⟨p.re+t,Real.sqrt (P t)⟩
          have hP : Continuous P := by dsimp [P]; fun_prop
          have hγ : Continuous γ := by
            have hh : Continuous (fun t : ℝ => (p.re+t : ℂ) + (Real.sqrt (P t) : ℂ) * Complex.I) := by
              fun_prop
            convert hh using 1
            ext t <;> simp [γ,Complex.ext_iff,Complex.exp_ofReal_re,Complex.exp_ofReal_im]
          have hγ0 : γ 0 = (p : ℂ) := by
            apply Complex.ext <;> simp [γ,P,Real.sqrt_sq_eq_abs,abs_of_pos p.im_pos]
          have hUI : IsOpen (((↑) : H2 → ℂ) '' U) :=
            UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hU
          let W : Set ℝ := {t | 0 < P t} ∩ γ ⁻¹' (((↑) : H2 → ℂ) '' U)
          have hW : IsOpen W :=
            (isOpen_lt continuous_const hP).inter (hUI.preimage hγ)
          have h0W : (0 : ℝ) ∈ W := by
            refine ⟨by simpa [P] using sq_pos_of_pos p.im_pos,?_⟩
            exact ⟨p,hpU,hγ0.symm⟩
          obtain ⟨δ,hδ,hδW⟩ := Metric.isOpen_iff.mp hW 0 h0W
          let t := δ / 2
          have ht : 0 < t := by dsimp [t]; linarith
          have htW : t ∈ W := hδW (by
            rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
            dsimp [t]; linarith)
          let z : H2 := ⟨γ t,Real.sqrt_pos.mpr htW.1⟩
          have hzU : z ∈ U := by
            obtain ⟨w,hw,he⟩ := htW.2
            have hwz : w = z := UpperHalfPlane.coe_injective he
            exact hwz ▸ hw
          have hkco : (k : ℂ) = -(g 1 1 : ℂ) / (g 1 0 : ℂ) := by simp [k]
          refine ⟨z,hzU,?_,?_⟩
          · rw [UpperHalfPlane.gl_smul_eq_self_iff_dist_sq_eq hneg htrace hc]
            rw [← hkco]
            change dist (γ t) (k : ℂ) ^ 2 = _
            rw [Complex.dist_eq,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
            have hsq : Real.sqrt (P t) ^ 2 = P t := Real.sq_sqrt htW.1.le
            have hi := (UpperHalfPlane.gl_smul_eq_self_iff_dist_sq_eq hneg htrace hc).mp hp
            rw [← hkco] at hi
            rw [Complex.dist_eq,← Complex.normSq_eq_norm_sq,Complex.normSq_apply] at hi
            simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
              UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,sub_zero] at hi
            simp only [γ,Complex.sub_re,Complex.sub_im,
              Complex.ofReal_re,Complex.ofReal_im,sub_zero]
            dsimp [P] at hsq
            nlinarith [hi,hsq]
          · intro hz
            have hre := congrArg UpperHalfPlane.re hz
            change p.re + t = p.re at hre
            have hre : t = 0 := by linarith [hre]
            exact ht.ne' hre
      have hpos : 0 < g.val.det := by
        by_contra hn
        have hneg : g.val.det < 0 := by
          have hle : g.val.det ≤ 0 := le_of_not_gt hn
          have hne := g.det_ne_zero
          exact lt_of_le_of_ne hle hne
        let p : H2 := ⟨c.chart x,c.upper x (hc hxU)⟩
        have hp : g • p = p := by
          have hh := hcoord ⟨x,hxU⟩
          simpa only [hx] using hh
        let V : Set H2 := {z | (z : ℂ) ∈ c.chart '' U}
        have hV : IsOpen V :=
          (c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU hc).preimage
            UpperHalfPlane.continuous_coe
        have hpV : p ∈ V := ⟨x,hxU,rfl⟩
        obtain ⟨z,hzV,hgz,hzp⟩ := negative_not_isolated g hneg p hp V hV hpV
        obtain ⟨y,hy,hcy⟩ := hzV
        have hyz : (⟨c.chart y,c.upper y (hc hy)⟩ : H2) = z :=
          UpperHalfPlane.coe_injective hcy
        have hJy : J y = y := by
          apply c.chart.toOpenPartialHomeomorph.injOn (hd hy) (hc hy)
          have hh := hcoord ⟨y,hy⟩
          rw [hyz,hgz] at hh
          exact (congrArg (fun z : H2 => (z : ℂ)) hh).symm.trans hcy.symm
        have hyx := hisolated y hy hJy
        apply hzp
        apply UpperHalfPlane.coe_injective
        exact hcy.symm.trans (congrArg c.chart hyx)
      exact ⟨hpos,UpperHalfPlane.mdifferentiable_smul hpos⟩
    have positive_mobius_involution_half_turn (g : GL (Fin 2) ℝ) (hpos : 0 < g.val.det)
        (hI : g • UpperHalfPlane.I = UpperHalfPlane.I)
        (hinv : Function.Involutive (fun z : H2 => g • z))
        (hne : ∃ z : H2, g • z ≠ z) :
        ∀ z : H2, ((g • z : H2) : ℂ) = -1 / (z : ℂ) := by
      have hnc : g ∉ Subgroup.center (GL (Fin 2) ℝ) := by
        intro hc
        have hall := UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mpr hc
        obtain ⟨z,hz⟩ := hne
        exact hz (hall z)
      have hell := UpperHalfPlane.isElliptic_of_exists_smul_eq_self hpos hnc ⟨_,hI⟩
      have hc : g 1 0 ≠ 0 := hell.c_ne_zero
      have hab := UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos hpos |>.mp hI
      have hgg : g * g ∈ Subgroup.center (GL (Fin 2) ℝ) := by
        apply UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp
        intro z
        simpa only [mul_smul] using hinv z
      obtain ⟨a,ha⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hgg
      change Matrix.scalar (Fin 2) a = g.val * g.val at ha
      have hoff := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 1 0) ha
      simp only [Matrix.mul_apply,Fin.sum_univ_two,
        Matrix.scalar_apply,Matrix.diagonal_apply,Fin.isValue,one_ne_zero,ite_false] at hoff
      have hdiag : g 0 0 = 0 := by
        have hp : 2 * g 0 0 * g 1 0 = 0 := by
          rw [← hab.1] at hoff
          nlinarith [hoff]
        have hprod : g 0 0 * g 1 0 = 0 := by linarith [hp]
        exact (mul_eq_zero.mp hprod).resolve_right hc
      have hdiag' : g 1 1 = 0 := hab.1.symm.trans hdiag
      intro z
      rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
      simp only [UpperHalfPlane.num,UpperHalfPlane.denom,hdiag,hdiag',hab.2,
        Complex.ofReal_zero,Complex.ofReal_neg,zero_mul,zero_add,add_zero]
      have hcz : (g 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
      have hz : (z : ℂ) ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        exact z.im_pos.ne' (by simpa using hi)
      field_simp
    have actual_complex_charted_atlas (H : ClosedHyperbolicMetric E) :
        letI : MetricSpace E := H.metric
        ∃ A : ChartedSpace ℂ E,
          (∀ e ∈ A.atlas, ∃ c : SmoothHyperbolicChart E,
            e = c.chart.toOpenPartialHomeomorph) ∧
          (∀ e ∈ A.atlas, ∀ y ∈ e.source, 0 < (e y).im) := by
      classical
      letI : MetricSpace E := H.metric
      choose c hc using H.smooth_hyperbolic
      let A : ChartedSpace ℂ E := {
        atlas := Set.range (fun x : E => (c x).chart.toOpenPartialHomeomorph)
        chartAt := fun x => (c x).chart.toOpenPartialHomeomorph
        mem_chart_source := hc
        chart_mem_atlas := fun x => ⟨x,rfl⟩ }
      refine ⟨A,?_,?_⟩
      · intro e he
        obtain ⟨x,rfl⟩ := he
        exact ⟨c x,rfl⟩
      · intro e he y hy
        obtain ⟨x,rfl⟩ := he
        exact (c x).upper y hy
    have plane_open_agreement (U : Set H2) (hU : IsOpen U) (hne : U.Nonempty)
        (e d : H2 ≃ᵢ H2) (hagree : ∀ z ∈ U, e z = d z) : e = d := by
      have hyperbolic_reference_point_rigidity : ∀ (t s : ℝ) (ht : t ≠ 0) (hs : 0 < s) (hs1 : s ≠ 1)
        (z w : UpperHalfPlane)
        (hA : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
        (hB : dist z (⟨⟨t,1⟩,by norm_num⟩ : UpperHalfPlane) =
          dist w (⟨⟨t,1⟩,by norm_num⟩ : UpperHalfPlane))
        (hC : dist z (⟨⟨0,s⟩,hs⟩ : UpperHalfPlane) =
          dist w (⟨⟨0,s⟩,hs⟩ : UpperHalfPlane)), z = w := by
        intro t s ht hs hs1 z w hA hB hC  
        have hz : z.im ≠ 0 := ne_of_gt z.im_pos
        have hw : w.im ≠ 0 := ne_of_gt w.im_pos
        have h1 := congrArg Real.cosh hA
        have h2 := congrArg Real.cosh hB
        have h3 := congrArg Real.cosh hC
        simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.I_re,
          UpperHalfPlane.I_im, sub_zero, one_pow, mul_one] at h1
        simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
          UpperHalfPlane.mk_im, one_pow, mul_one] at h2
        simp only [UpperHalfPlane.cosh_dist', UpperHalfPlane.mk_re,
          UpperHalfPlane.mk_im, sub_zero] at h3
        have H1 : (z.re ^ 2 + z.im ^ 2 + 1) * w.im =
            (w.re ^ 2 + w.im ^ 2 + 1) * z.im := by
          field_simp at h1
          nlinarith [h1]
        have H2 : ((z.re - t) ^ 2 + z.im ^ 2 + 1) * w.im =
            ((w.re - t) ^ 2 + w.im ^ 2 + 1) * z.im := by
          field_simp at h2
          nlinarith [h2]
        have H3 : (z.re ^ 2 + z.im ^ 2 + s ^ 2) * w.im =
            (w.re ^ 2 + w.im ^ 2 + s ^ 2) * z.im := by
          field_simp at h3
          nlinarith [h3]
        have hs2 : s ^ 2 - 1 ≠ 0 := by
          have hm : (s - 1) * (s + 1) ≠ 0 :=
            mul_ne_zero (sub_ne_zero.mpr hs1) (by linarith)
          intro h
          apply hm
          nlinarith [h]
        have hp : (s ^ 2 - 1) * (w.im - z.im) = 0 := by
          nlinarith [H1,H3]
        have him : z.im = w.im := by
          have he := (mul_eq_zero.mp hp).resolve_left hs2
          linarith
        have hp' : t * (z.re - w.re) * z.im = 0 := by
          rw [← him] at H1 H2
          nlinarith [H1,H2]
        have hre : z.re = w.re := by
          have he := (mul_eq_zero.mp hp').resolve_right hz
          have he' := (mul_eq_zero.mp he).resolve_left ht
          linarith
        apply UpperHalfPlane.ext
        exact Complex.ext hre him
      obtain ⟨p,hp⟩ := hne
      let a : H2 ≃ᵢ H2 := IsometryEquiv.constSMul p.toSL2R
      have ha : a UpperHalfPlane.I = p := p.toSL2R_smul_I
      let V : Set H2 := a ⁻¹' U
      have hV : IsOpen V := hU.preimage a.continuous
      have hIV : UpperHalfPlane.I ∈ V := by change a UpperHalfPlane.I ∈ U; rw [ha]; exact hp
      let horizontal : ℝ → H2 := fun t => ⟨⟨t,1⟩,by norm_num⟩
      have hhor : Continuous horizontal := by
        apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
        have hh : Continuous (fun t : ℝ => (t : ℂ) + Complex.I) :=
          Complex.continuous_ofReal.add continuous_const
        convert hh using 1
        ext t <;> simp [horizontal,Complex.ext_iff]
      have hhor0 : horizontal 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [horizontal]
      have hvert0 : verticalPath 0 = UpperHalfPlane.I := by
        apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
      let W : Set ℝ := horizontal ⁻¹' V ∩ verticalPath ⁻¹' V
      have hW : IsOpen W :=
        (hV.preimage hhor).inter (hV.preimage verticalPath_isometry.continuous)
      have h0W : (0 : ℝ) ∈ W := by
        exact ⟨by change horizontal 0 ∈ V; rw [hhor0]; exact hIV,
          by change verticalPath 0 ∈ V; rw [hvert0]; exact hIV⟩
      obtain ⟨δ,hδ,hδW⟩ := Metric.isOpen_iff.mp hW 0 h0W
      let r := δ / 2
      have hr : 0 < r := by dsimp [r]; linarith
      have hrW : r ∈ W := hδW (by
        rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hr]
        dsimp [r]
        linarith)
      have heI : e (a UpperHalfPlane.I) = d (a UpperHalfPlane.I) := hagree _ hIV
      have heB : e (a (horizontal r)) = d (a (horizontal r)) := hagree _ hrW.1
      have heC : e (a (verticalPath r)) = d (a (verticalPath r)) := hagree _ hrW.2
      have hs1 : Real.exp r ≠ 1 := by
        intro h
        have hh : Real.exp r = Real.exp 0 := by simpa using h
        have := Real.exp_injective hh
        exact hr.ne' this
      apply IsometryEquiv.ext
      intro z
      have eqnorm : a.symm (e.symm (d z)) = a.symm z := by
        refine hyperbolic_reference_point_rigidity r (Real.exp r) hr.ne' (Real.exp_pos r) hs1 _ _ ?_ ?_ ?_
        · calc
            dist (a.symm (e.symm (d z))) UpperHalfPlane.I =
                dist (d z) (e (a UpperHalfPlane.I)) := by
                  rw [← a.dist_eq, a.apply_symm_apply, ← e.dist_eq, e.apply_symm_apply]
            _ = dist (d z) (d (a UpperHalfPlane.I)) := by rw [heI]
            _ = dist (a.symm z) UpperHalfPlane.I := by
              rw [d.dist_eq]
              simpa only [a.symm_apply_apply] using (a.symm.dist_eq z (a UpperHalfPlane.I)).symm
        · change dist (a.symm (e.symm (d z))) (horizontal r) = dist (a.symm z) (horizontal r)
          calc
            dist (a.symm (e.symm (d z))) (horizontal r) = dist (d z) (e (a (horizontal r))) := by
              rw [← a.dist_eq, a.apply_symm_apply, ← e.dist_eq, e.apply_symm_apply]
            _ = dist (d z) (d (a (horizontal r))) := by rw [heB]
            _ = dist (a.symm z) (horizontal r) := by
              rw [d.dist_eq]
              simpa only [a.symm_apply_apply] using (a.symm.dist_eq z (a (horizontal r))).symm
        · change dist (a.symm (e.symm (d z))) (verticalPath r) = dist (a.symm z) (verticalPath r)
          calc
            dist (a.symm (e.symm (d z))) (verticalPath r) = dist (d z) (e (a (verticalPath r))) := by
              rw [← a.dist_eq, a.apply_symm_apply, ← e.dist_eq, e.apply_symm_apply]
            _ = dist (d z) (d (a (verticalPath r))) := by rw [heC]
            _ = dist (a.symm z) (verticalPath r) := by
              rw [d.dist_eq]
              simpa only [a.symm_apply_apply] using (a.symm.dist_eq z (a (verticalPath r))).symm
      have hz : e.symm (d z) = z := a.symm.injective eqnorm
      have hh := congrArg e hz
      simpa using hh.symm
    have actual_hyperbolic_atlas_transition (c d : SmoothHyperbolicChart E)
        (hne : (c.chart.source ∩ d.chart.source).Nonempty) :
        ∃ T : H2 ≃ᵢ H2, ∀ (x : E) (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source),
          T (⟨c.chart x,c.upper x hc⟩ : H2) = (⟨d.chart x,d.upper x hd⟩ : H2) := by
      classical
      let U : Set E := c.chart.source ∩ d.chart.source
      have hU : IsOpen U := c.chart.toOpenPartialHomeomorph.open_source.inter
        d.chart.toOpenPartialHomeomorph.open_source
      let V : Set H2 := {z | (z : ℂ) ∈ c.chart '' U}
      have hV : IsOpen V :=
        (c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU Set.inter_subset_left).preimage
          UpperHalfPlane.continuous_coe
      have hVne : V.Nonempty := by
        obtain ⟨x,hxc,hxd⟩ := hne
        exact ⟨⟨c.chart x,c.upper x hxc⟩,x,⟨hxc,hxd⟩,rfl⟩
      have preimage (z : V) : ∃ x : U, c.chart x.val = (z.val : ℂ) := by
        obtain ⟨x,hx,hcx⟩ := z.property
        exact ⟨⟨x,hx⟩,hcx⟩
      let lift : V → U := fun z => Classical.choose (preimage z)
      have hlift (z : V) : c.chart (lift z).val = (z.val : ℂ) :=
        Classical.choose_spec (preimage z)
      have hcoords (z : V) :
          (⟨c.chart (lift z).val,c.upper (lift z).val (lift z).property.1⟩ : H2) = z.val :=
        UpperHalfPlane.coe_injective (hlift z)
      let F : V → H2 := fun z =>
        ⟨d.chart (lift z).val,d.upper (lift z).val (lift z).property.2⟩
      have hF : Isometry F := Isometry.of_dist_eq (by
        intro y z
        change dist (⟨d.chart (lift y).val,_⟩ : H2)
          (⟨d.chart (lift z).val,_⟩ : H2) = dist y z
        rw [← d.metric_preserving ⟨(lift y).val,(lift y).property.2⟩
          ⟨(lift z).val,(lift z).property.2⟩,
          c.metric_preserving ⟨(lift y).val,(lift y).property.1⟩
          ⟨(lift z).val,(lift z).property.1⟩,hcoords y,hcoords z]
        rfl)
      obtain ⟨T,hT⟩ := local_plane_extension V hV hVne F hF
      refine ⟨T,?_⟩
      intro x hc hd
      let z : V := ⟨⟨c.chart x,c.upper x hc⟩,x,⟨hc,hd⟩,rfl⟩
      have hxlift : (lift z).val = x :=
        c.chart.toOpenPartialHomeomorph.injOn (lift z).property.1 hc (hlift z)
      change T z.val = (⟨d.chart x,d.upper x hd⟩ : H2)
      rw [hT z]
      apply UpperHalfPlane.coe_injective
      exact congrArg d.chart hxlift
    have actual_hyperbolic_atlas_cocycle (c d a : SmoothHyperbolicChart E)
        (hne : (c.chart.source ∩ d.chart.source ∩ a.chart.source).Nonempty)
        (Tcd Tda Tca : H2 ≃ᵢ H2)
        (hcd : ∀ x (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source),
          Tcd (⟨c.chart x,c.upper x hc⟩ : H2) = (⟨d.chart x,d.upper x hd⟩ : H2))
        (hda : ∀ x (hd : x ∈ d.chart.source) (ha : x ∈ a.chart.source),
          Tda (⟨d.chart x,d.upper x hd⟩ : H2) = (⟨a.chart x,a.upper x ha⟩ : H2))
        (hca : ∀ x (hc : x ∈ c.chart.source) (ha : x ∈ a.chart.source),
          Tca (⟨c.chart x,c.upper x hc⟩ : H2) = (⟨a.chart x,a.upper x ha⟩ : H2)) :
        Tcd.trans Tda = Tca := by
      let U : Set E := c.chart.source ∩ d.chart.source ∩ a.chart.source
      have hU : IsOpen U :=
        (c.chart.toOpenPartialHomeomorph.open_source.inter
          d.chart.toOpenPartialHomeomorph.open_source).inter
            a.chart.toOpenPartialHomeomorph.open_source
      let V : Set H2 := {z | (z : ℂ) ∈ c.chart '' U}
      have hV : IsOpen V :=
        (c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU
          (fun x hx => hx.1.1)).preimage UpperHalfPlane.continuous_coe
      have hVne : V.Nonempty := by
        obtain ⟨x,hx⟩ := hne
        exact ⟨⟨c.chart x,c.upper x hx.1.1⟩,x,hx,rfl⟩
      apply plane_open_agreement V hV hVne
      intro z hz
      obtain ⟨x,hx,hcx⟩ := hz
      have hcz : (⟨c.chart x,c.upper x hx.1.1⟩ : H2) = z :=
        UpperHalfPlane.coe_injective hcx
      rw [← hcz,IsometryEquiv.trans_apply,hcd x hx.1.1 hx.1.2,
        hda x hx.1.2 hx.2,hca x hx.1.1 hx.2]
    have half_turn_plane_coordinate : ∃ e : H2 ≃ₜ ℝ × ℝ, e UpperHalfPlane.I = 0 ∧
        ∀ z w : H2, (w : ℂ) = -1 / (z : ℂ) → e w = -e z := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        have cayley_half_turn (z w : H2) (h : (w : ℂ) = -1 / (z : ℂ)) :
            (cayleyOpen w : ℂ) = -(cayleyOpen z : ℂ) := by
          have hz : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
          have hp : (z : ℂ) + Complex.I ≠ 0 := by
            intro he
            have hh := congrArg Complex.im he
            simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at hh
            have hi : 0 < (z : ℂ).im := z.im_pos
            linarith
          have hw : (w : ℂ) + Complex.I ≠ 0 := by
            intro he
            have hh := congrArg Complex.im he
            simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at hh
            have hi : 0 < (w : ℂ).im := w.im_pos
            linarith
          change ((w : ℂ) - Complex.I) / ((w : ℂ) + Complex.I) =
            -(((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I))
          rw [h] at hw ⊢
          have hd : (-1 : ℂ) + (z : ℂ) * Complex.I ≠ 0 := by
            intro he
            apply hw
            apply (mul_left_cancel₀ hz)
            calc
              (z : ℂ) * (-1 / (z : ℂ) + Complex.I) = -1 + (z : ℂ) * Complex.I := by field_simp
              _ = (z : ℂ) * 0 := by rw [he,mul_zero]
          field_simp [hz,hp,hd]
          ring_nf
          simp only [Complex.I_sq]
          ring
        let e : H2 ≃ₜ ℝ × ℝ := cayleyHomeomorph.trans
          ((Homeomorph.unitBall (E := ℂ)).symm.trans Complex.equivRealProdCLM.toHomeomorph)
        refine ⟨e, ?_, ?_⟩
        · change Complex.equivRealProdCLM ((Homeomorph.unitBall (E := ℂ)).symm (cayleyHomeomorph UpperHalfPlane.I)) = 0
          have hI : cayleyHomeomorph UpperHalfPlane.I = Homeomorph.unitBall (0 : ℂ) := by
            apply Subtype.ext
            change ((UpperHalfPlane.I : ℂ) - Complex.I) / ((UpperHalfPlane.I : ℂ) + Complex.I) = (Homeomorph.unitBall (0 : ℂ) : ℂ)
            simp
          rw [hI,Homeomorph.symm_apply_apply]
          exact map_zero _
        · intro z w hw
          have hc := cayley_half_turn z w hw
          change Complex.equivRealProdCLM ((Homeomorph.unitBall (E := ℂ)).symm (cayleyOpen w)) =
            -Complex.equivRealProdCLM ((Homeomorph.unitBall (E := ℂ)).symm (cayleyOpen z))
          change Complex.equivRealProdCLM ((Real.sqrt (1 - ‖(cayleyOpen w : ℂ)‖ ^ 2))⁻¹ • (cayleyOpen w : ℂ)) =
            -Complex.equivRealProdCLM ((Real.sqrt (1 - ‖(cayleyOpen z : ℂ)‖ ^ 2))⁻¹ • (cayleyOpen z : ℂ))
          rw [hc,norm_neg,smul_neg,map_neg]
      )
    have normalized_positive_mobius_half_turn (g : GL (Fin 2) ℝ) (hpos : 0 < g.val.det)
        (p : H2) (hp : g • p = p)
        (hinv : Function.Involutive (fun z : H2 => g • z))
        (hne : ∃ z : H2, g • z ≠ z) :
        ∃ n : H2 ≃ₜ H2, n p = UpperHalfPlane.I ∧
          ∀ z : H2, (n (g • z) : ℂ) = -1 / (n z : ℂ) := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        let a := p.toSL2R
        let A : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ a
        let q : GL (Fin 2) ℝ := A⁻¹ * g * A
        let n : H2 ≃ₜ H2 := (IsometryEquiv.constSMul a).symm.toHomeomorph
        have hAI : A • UpperHalfPlane.I = p := by
          change a • UpperHalfPlane.I = p
          exact p.toSL2R_smul_I
        have hn (z : H2) : n z = A⁻¹ • z := by
          change a⁻¹ • z = A⁻¹ • z
          change (Matrix.SpecialLinearGroup.mapGL ℝ (a⁻¹)) • z = _
          rw [map_inv]
        have hq (z : H2) : q • z = A⁻¹ • (g • (A • z)) := by simp only [q,mul_smul]
        have hdetA : A.det = 1 := by simp [A]
        have hposq : 0 < q.val.det := by
          change 0 < q.det.val
          have hpos' : 0 < g.det.val := hpos
          simpa only [q,map_mul,map_inv,hdetA,inv_one,one_mul,mul_one] using hpos'
        have hqI : q • UpperHalfPlane.I = UpperHalfPlane.I := by
          rw [hq,hAI,hp,←hAI,inv_smul_smul]
        have hqinv : Function.Involutive (fun z : H2 => q • z) := by
          intro z
          change q • (q • z) = z
          have hh : g • (g • (A • z)) = A • z := hinv _
          rw [hq,hq,smul_inv_smul,hh,inv_smul_smul]
        have hqne : ∃ z : H2, q • z ≠ z := by
          obtain ⟨z,hz⟩ := hne
          refine ⟨A⁻¹ • z,?_⟩
          intro he
          apply hz
          have hh := congrArg (fun w : H2 => A • w) he
          simpa only [hq,smul_inv_smul] using hh
        have hh := positive_mobius_involution_half_turn q hposq hqI hqinv hqne
        refine ⟨n,?_,?_⟩
        · rw [hn,←hAI,inv_smul_smul]
        · intro z
          have haction : n (g • z) = q • n z := by
            rw [hn,hn,hq,smul_inv_smul]
          rw [haction]
          exact hh (n z)
      )
    have actual_normalized_central_chart (c : SmoothHyperbolicChart E) (J : E ≃ₜ E)
        (U : Set E) (hU : IsOpen U) (x : E) (hxU : x ∈ U)
        (hc : U ⊆ c.chart.source) (hJU : Set.MapsTo J U U)
        (n : H2 ≃ₜ H2)
        (hn : n (⟨c.chart x,c.upper x (hc hxU)⟩ : H2) = UpperHalfPlane.I)
        (hhalf : ∀ y : U,
          ((n (⟨c.chart (J y.val),c.upper (J y.val) (hc (hJU y.property))⟩ : H2)) : ℂ) =
            -1 / ((n (⟨c.chart y.val,c.upper y.val (hc y.property)⟩ : H2)) : ℂ)) :
        ∃ e : OpenPartialHomeomorph E (ℝ × ℝ), x ∈ e.source ∧ e x = 0 ∧
          ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ℝ × ℝ) r ⊆ e.target ∧
            ∀ z ∈ Metric.ball (0 : ℝ × ℝ) r, J (e.symm z) = e.symm (-z) := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        obtain ⟨D,hDI,hD⟩ := half_turn_plane_coordinate
        let a := (c.chart.toOpenPartialHomeomorph.restr U).trans UpperHalfPlane.ofComplex
        let e := a.transHomeomorph (n.trans D)
        have hs (y : E) (hy : y ∈ U) : y ∈ e.source := by
          change y ∈ (c.chart.toOpenPartialHomeomorph.restr U).source ∧
            c.chart y ∈ UpperHalfPlane.ofComplex.source
          constructor
          · rw [OpenPartialHomeomorph.restr_source' _ _ hU]
            exact ⟨hc hy,hy⟩
          · simp only [UpperHalfPlane.ofComplex,OpenPartialHomeomorph.symm_source,
              Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
            change c.chart y ∈ Set.range ((↑) : H2 → ℂ)
            exact ⟨⟨c.chart y,c.upper y (hc hy)⟩,rfl⟩
        have hu (y : E) (hy : y ∈ e.source) : y ∈ U := by
          change y ∈ (c.chart.toOpenPartialHomeomorph.restr U).source ∧ _ at hy
          rw [OpenPartialHomeomorph.restr_source' _ _ hU] at hy
          exact hy.1.2
        have he (y : E) (hy : y ∈ U) :
            e y = D (n (⟨c.chart y,c.upper y (hc hy)⟩ : H2)) := by
          change D (n (UpperHalfPlane.ofComplex (c.chart y))) = _
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos (c.upper y (hc hy))]
        have hx0 : e x = 0 := by rw [he x hxU,hn,hDI]
        have h0 : (0 : ℝ × ℝ) ∈ e.target := hx0 ▸ e.map_source (hs x hxU)
        obtain ⟨ε,hε,hballε⟩ := Metric.isOpen_iff.mp e.open_target 0 h0
        let r : ℝ := ε / 2
        have hr : 0 < r := by dsimp [r]; positivity
        have hball : Metric.closedBall (0 : ℝ × ℝ) r ⊆ e.target :=
          (Metric.closedBall_subset_ball (by dsimp [r]; linarith : r < ε)).trans hballε
        refine ⟨e,hs x hxU,hx0,r,hr,hball,?_⟩
        intro z hz
        have hzT : z ∈ e.target := hball (Metric.ball_subset_closedBall hz)
        have hyS := e.map_target hzT
        have hyU := hu (e.symm z) hyS
        have hJyU := hJU hyU
        have heJ : e (J (e.symm z)) = - e (e.symm z) := by
          rw [he _ hJyU,he _ hyU]
          exact hD _ _ (hhalf ⟨e.symm z,hyU⟩)
        apply (e.eq_symm_apply (hs _ hJyU) _).mpr
        · rw [heJ,e.right_inv hzT]
        · apply hball
          exact Metric.ball_subset_closedBall (by simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hz)
      )
    have actual_germ_involution (J : E ≃ₜ E) (hJinv : Function.Involutive J)
        (c : SmoothHyperbolicChart E) (U : Set E) (hU : IsOpen U) (x : E)
        (hxU : x ∈ U) (hfx : J x = x)
        (hc : U ⊆ c.chart.source) (hd : Set.MapsTo J U c.chart.source)
        (hisolated : ∀ y ∈ U, J y = y → y = x)
        (g : GL (Fin 2) ℝ) (e : H2 ≃ᵢ H2) (he : ∀ z : H2, e z = g • z)
        (hcoord : ∀ y : U,
          g • (⟨c.chart y.val,c.upper y.val (hc y.property)⟩ : H2) =
            (⟨c.chart (J y.val),c.upper (J y.val) (hd y.property)⟩ : H2))
     :
        Function.Involutive (fun z : H2 => g • z) ∧ ∃ z : H2, g • z ≠ z := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        let V := U ∩ J ⁻¹' U
        have hV : IsOpen V := hU.inter (hU.preimage J.continuous)
        have hxV : x ∈ V := ⟨hxU,by change J x ∈ U; rw [hfx]; exact hxU⟩
        have hJV : Set.MapsTo J V V := by
          intro y hy
          exact ⟨hy.2,by change J (J y) ∈ U; rw [hJinv]; exact hy.1⟩
        let a := (c.chart.toOpenPartialHomeomorph.restr V).trans UpperHalfPlane.ofComplex
        have hs (y : E) (hy : y ∈ V) : y ∈ a.source := by
          change y ∈ (c.chart.toOpenPartialHomeomorph.restr V).source ∧
            c.chart y ∈ UpperHalfPlane.ofComplex.source
          constructor
          · rw [OpenPartialHomeomorph.restr_source' _ _ hV]
            exact ⟨hc hy.1,hy⟩
          · simp only [UpperHalfPlane.ofComplex,OpenPartialHomeomorph.symm_source,
              Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
            exact ⟨⟨c.chart y,c.upper y (hc hy.1)⟩,rfl⟩
        have hu (y : E) (hy : y ∈ a.source) : y ∈ V := by
          change y ∈ (c.chart.toOpenPartialHomeomorph.restr V).source ∧ _ at hy
          rw [OpenPartialHomeomorph.restr_source' _ _ hV] at hy
          exact hy.1.2
        have ha (y : E) (hy : y ∈ V) : a y = (⟨c.chart y,c.upper y (hc hy.1)⟩ : H2) := by
          change UpperHalfPlane.ofComplex (c.chart y) = _
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos (c.upper y (hc hy.1))]
        have heJ (y : E) (hy : y ∈ V) : e (a y) = a (J y) := by
          rw [he,ha _ hy,ha _ (hJV hy)]
          exact hcoord ⟨y,hy.1⟩
        have hpT : a x ∈ a.target := a.map_source (hs x hxV)
        have hesquare (z : H2) (hz : z ∈ a.target) : e (e z) = z := by
          have hy := hu (a.symm z) (a.map_target hz)
          rw [←a.right_inv hz,heJ _ hy,heJ _ (hJV hy),hJinv,a.right_inv hz]
        have heinvol := plane_extension_square_rigidity a.target a.open_target ⟨a x,hpT⟩ e hesquare
        constructor
        · intro z
          change g • (g • z) = z
          rw [←he,←he]
          exact heinvol z
        · haveI : Filter.NeBot (𝓝[≠] (a x)) := inferInstance
          have hQ : a.target ∈ 𝓝[≠] (a x) :=
            mem_nhdsWithin_of_mem_nhds (a.open_target.mem_nhds hpT)
          obtain ⟨z,hzQ,hzne⟩ := Filter.nonempty_of_mem (Filter.inter_mem hQ self_mem_nhdsWithin)
          refine ⟨z,?_⟩
          intro hzfix
          have hy := hu (a.symm z) (a.map_target hzQ)
          have hJy : J (a.symm z) = a.symm z := by
            apply a.injOn (hs _ (hJV hy)) (hs _ hy)
            rw [←heJ _ hy,a.right_inv hzQ,he,hzfix]
          have hyx := hisolated _ hy.1 hJy
          apply hzne
          change z = a x
          rw [←a.right_inv hzQ,hyx]
      )
    have actual_positive_mobius_germ_at_fixed_point :
        ∃ x : E, J x = x ∧ ∃ (c : SmoothHyperbolicChart E) (U : Set E),
          ∃ hU : IsOpen U, ∃ hxU : x ∈ U,
          ∃ hc : U ⊆ c.chart.source, ∃ hd : Set.MapsTo J U c.chart.source,
          ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧
            MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) (fun z : H2 => g • z) ∧
            ∃ e : H2 ≃ᵢ H2, (∀ z : H2, e z = g • z) ∧
              (∀ y ∈ U, J y = y → y = x) ∧
            ∀ y : U,
              g • (⟨c.chart y.val,c.upper y.val (hc y.property)⟩ : H2) =
                (⟨c.chart (J y.val),c.upper (J y.val) (hd y.property)⟩ : H2) := by
      obtain ⟨x,hx,V,hV,hxV,hJV,hisolated⟩ := isolated_invariant_fixed_neighborhood
      obtain ⟨c,d,hxc,hJxd,W,hW,hxW,hcW,hdW,e,he⟩ := local_chart_extension x
      have hxd : x ∈ d.chart.source := by simpa only [hx] using hJxd
      obtain ⟨T,hT⟩ := actual_hyperbolic_atlas_transition d c ⟨x,hxd,hxc⟩
      let U : Set E := (V ∩ W) ∩ J ⁻¹' c.chart.source
      have hU : IsOpen U := (hV.inter hW).inter
        (c.chart.toOpenPartialHomeomorph.open_source.preimage J.continuous)
      have hxU : x ∈ U := ⟨⟨hxV,hxW⟩,by change J x ∈ c.chart.source; rw [hx]; exact hxc⟩
      have hc : U ⊆ c.chart.source := fun y hy => hcW hy.1.2
      have hd : Set.MapsTo J U c.chart.source := fun y hy => hy.2
      obtain ⟨g,hg⟩ := axis_metric_isometry_gl_representation (e.trans T)
      have hcoord (y : U) :
          g • (⟨c.chart y.val,c.upper y.val (hc y.property)⟩ : H2) =
            (⟨c.chart (J y.val),c.upper (J y.val) (hd y.property)⟩ : H2) := by
        rw [← hg,IsometryEquiv.trans_apply]
        rw [he ⟨y.val,y.property.1.2⟩]
        exact hT (J y.val) (hdW y.property.1.2) (hd y.property)
      have hisolatedU (y : E) (hy : y ∈ U) (hyJ : J y = y) : y = x :=
        (hisolated y hy.1.1).mp hyJ
      have hpos := actual_chart_isolated_fixed_mobius_orientation J c x U hU hxU hc hd
        hx hisolatedU g hcoord
      exact ⟨x,hx,c,U,hU,hxU,hc,hd,g,hpos.1,hpos.2,e.trans T,hg,hisolatedU,hcoord⟩
    obtain ⟨x,hx,c,U,hU,hxU,hc,hd,g,hpos,hmd,e,he,hisolated,hcoord⟩ :=
      actual_positive_mobius_germ_at_fixed_point
    have hginv_nontrivial := actual_germ_involution J hJinv c U hU x hxU hx
      hc hd hisolated g e he hcoord
    let p : H2 := ⟨c.chart x,c.upper x (hc hxU)⟩
    have hp : g • p = p := by
      have hh := hcoord ⟨x,hxU⟩
      simpa only [p,hx] using hh
    obtain ⟨n,hn,hhalf⟩ := normalized_positive_mobius_half_turn g hpos p hp
      hginv_nontrivial.1 hginv_nontrivial.2
    let V : Set E := U ∩ J ⁻¹' U
    have hV : IsOpen V := hU.inter (hU.preimage J.continuous)
    have hxV : x ∈ V := ⟨hxU,by change J x ∈ U; rw [hx]; exact hxU⟩
    have hJV : Set.MapsTo J V V := by
      intro y hy
      exact ⟨hy.2,by change J (J y) ∈ U; rw [hJinv]; exact hy.1⟩
    have hcV : V ⊆ c.chart.source := fun y hy => hc hy.1
    have hhalfV (y : V) :
        ((n (⟨c.chart (J y.val),c.upper (J y.val) (hcV (hJV y.property))⟩ : H2)) : ℂ) =
          -1 / ((n (⟨c.chart y.val,c.upper y.val (hcV y.property)⟩ : H2)) : ℂ) := by
      rw [←hcoord ⟨y.val,y.property.1⟩]
      exact hhalf _
    obtain ⟨actual_central_chart,hxchart,hchartx,r,hr,hball,hcentral⟩ :=
      actual_normalized_central_chart c J V hV x hxV hcV hJV n hn hhalfV
    have J_preserves_puncture : ∀ y ∈ ({x}ᶜ : Set E), J y ∈ ({x}ᶜ : Set E) := by
      intro y hy heq
      apply hy
      change y = x
      have hh := congrArg J heq
      rw [hJinv y,hx] at hh
      exact hh
    have actual_J_global_orientation_identity :=
      actual_global_orientation_from_half_turn_chart J x actual_central_chart hxchart hchartx
        J_preserves_puncture r hr hball hcentral
    have actual_J_preserves_every_local_orientation_class : ∀ q : E,
        ∃ hpres : ∀ y ∈ ({q}ᶜ : Set E), J y ∈ ({J q}ᶜ : Set E),
          pairRelativeHomologyMap ({q}ᶜ : Set E) ({J q}ᶜ : Set E)
            ⟨J,J.continuous⟩ hpres 2
              (homologyToRelative E ({q}ᶜ : Set E) 2 orientation_class) =
                homologyToRelative E ({J q}ᶜ : Set E) 2 orientation_class := by
      set_option backward.isDefEq.respectTransparency false in
      exact (by
        intro q
        have hpres : ∀ y ∈ ({q}ᶜ : Set E), J y ∈ ({J q}ᶜ : Set E) := by
          intro y hy heq
          exact hy (J.injective heq)
        refine ⟨hpres,?_⟩
        have hn := pairRelativeHomologyMap_commutes ({q}ᶜ : Set E) ({J q}ᶜ : Set E)
          (⟨J,J.continuous⟩ : C(E,E)) hpres 2
        change homologyToRelative E ({q}ᶜ : Set E) 2 ≫
            pairRelativeHomologyMap ({q}ᶜ : Set E) ({J q}ᶜ : Set E)
              ⟨J,J.continuous⟩ hpres 2 =
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (⟨J,J.continuous⟩ : C(E,E)))) ≫
              homologyToRelative E ({J q}ᶜ : Set E) 2 at hn
        rw [actual_J_global_orientation_identity] at hn
        have hp := congrArg (fun k : integralHomology E 2 ⟶
          relativeHomology E ({J q}ᶜ : Set E) 2 => k orientation_class) hn
        change pairRelativeHomologyMap ({q}ᶜ : Set E) ({J q}ᶜ : Set E)
            ⟨J,J.continuous⟩ hpres 2
              (homologyToRelative E ({q}ᶜ : Set E) 2 orientation_class) =
                homologyToRelative E ({J q}ᶜ : Set E) 2 orientation_class at hp
        exact hp)
    have actual_positive_chart_family_complex_manifold (c : E → SmoothHyperbolicChart E)
        (hc : ∀ x : E, x ∈ (c x).chart.source)
        (hpositive : ∀ a b : E, ((c a).chart.source ∩ (c b).chart.source).Nonempty →
          ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧
            ∀ x (ha : x ∈ (c a).chart.source) (hb : x ∈ (c b).chart.source),
              g • (⟨(c a).chart x,(c a).upper x ha⟩ : H2) =
                (⟨(c b).chart x,(c b).upper x hb⟩ : H2)) :
        ∃ A : ChartedSpace ℂ E, @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ∞ E _ A := by
      exact positive_hyperbolic_chart_family_complex_manifold c hc hpositive
    have positive_mobius_germs_holomorphic_map {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
        (f : C(X,X))
        (hcoords : ∀ x : X, ∃ (U : Set X) (g : GL (Fin 2) ℝ),
          IsOpen U ∧ x ∈ U ∧ U ⊆ (chartAt ℂ x).source ∧
            Set.MapsTo f U (chartAt ℂ (f x)).source ∧ 0 < g.val.det ∧
              ∀ y ∈ U, ∃ hy : 0 < (chartAt ℂ x y).im,
                ((g • (⟨chartAt ℂ x y,hy⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) =
                  chartAt ℂ (f x) (f y)) :
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f := by
      exact _root_.positive_mobius_germs_holomorphic_map f hcoords
    have actual_coherent_positive_chart_family
        (M : HyperellipticModel E S) (H : ClosedHyperbolicMetric E) :
        letI : MetricSpace E := H.metric
        ∃ z : CurveComplexGenusTwo.CWHurewicz.H E 2,
        ∃ φ : relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ≅ ModuleCat.of ℤ ℤ,
        ∃ c : E → SmoothHyperbolicChart E,
          (∀ x : E, x ∈ (c x).chart.source) ∧
        ∃ e : E → OpenPartialHomeomorph E ℂ,
          (∀ a, (e a).source = (c a).chart.source) ∧
          (∀ a y (hy : y ∈ (c a).chart.source),
            let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
            e a y = D (⟨(c a).chart y,(c a).upper y hy⟩ : H2)) ∧
          (∀ a (y : (e a).source),
            let A : Set (e a).source := {q | q.val ≠ y.val}
            let k : C((e a).source,ℂ) := ⟨fun q => e a q.val-e a y.val,
              ((e a).continuousOn.comp_continuous continuous_subtype_val (fun q => q.property)).sub continuous_const⟩
            ∃ v : relativeHomology (e a).source A 2,
            ∃ hpres : ∀ q ∈ A, k q ∈ ({0}ᶜ : Set ℂ),
              pairRelativeHomologyMap A ({y.val}ᶜ : Set E) (ReflectionGermProof.inclusion (e a).source)
                (fun q hq => hq) 2 v = homologyToRelative E ({y.val}ᶜ : Set E) 2 z ∧
              0 < φ.hom (pairRelativeHomologyMap A ({0}ᶜ : Set ℂ) k hpres 2 v)) ∧
          ∀ a b : E, ((c a).chart.source ∩ (c b).chart.source).Nonempty →
            ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧
              ∀ x (ha : x ∈ (c a).chart.source) (hb : x ∈ (c b).chart.source),
                g • (⟨(c a).chart x,(c a).upper x ha⟩ : H2) =
                  (⟨(c b).chart x,(c b).upper x hb⟩ : H2) := by
      letI : MetricSpace E := H.metric
      have positive_choices (M : HyperellipticModel E S) (G : ClosedHyperbolicMetric E) :
          letI : MetricSpace E := G.metric
          ∃ z : CurveComplexGenusTwo.CWHurewicz.H E 2, z ≠ 0 ∧
          ∃ φ : relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ≅ ModuleCat.of ℤ ℤ,
            ∀ x : E, ∃ c : SmoothHyperbolicChart E, x ∈ c.chart.source ∧
              ∃ e : OpenPartialHomeomorph E ℂ, e.source = c.chart.source ∧
                (∀ y (hy : y ∈ c.chart.source),
                  let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
                  e y = D (⟨c.chart y,c.upper y hy⟩ : H2)) ∧
                ∀ y : e.source,
                  let A : Set e.source := {q | q.val ≠ y.val}
                  let k : C(e.source,ℂ) := ⟨fun q => e q.val-e y.val,
                    (e.continuousOn.comp_continuous continuous_subtype_val (fun q => q.property)).sub continuous_const⟩
                  ∃ v : relativeHomology e.source A 2,
                    ∃ hpres : ∀ q ∈ A, k q ∈ ({0}ᶜ : Set ℂ),
                      pairRelativeHomologyMap A ({y.val}ᶜ : Set E) (ReflectionGermProof.inclusion e.source)
                        (fun q hq => hq) 2 v = homologyToRelative E ({y.val}ᶜ : Set E) 2 z ∧
                      0 < φ.hom (pairRelativeHomologyMap A ({0}ᶜ : Set ℂ) k hpres 2 v) := by
        have orientation_sections (M : HyperellipticModel E S) :
            ∃ z : CurveComplexGenusTwo.CWHurewicz.H E 2, z ≠ 0 ∧
              (∀ x : E, homologyToRelative E ({x}ᶜ : Set E) 2 z ≠ 0) ∧
              ∃ φ : relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ≅ ModuleCat.of ℤ ℤ,
                ∀ e : OpenPartialHomeomorph E ℂ,
                  let W := e.source
                  let A (x : W) : Set W := {y | y.val ≠ x.val}
                  let P : Set ℂ := {0}ᶜ
                  let k (x : W) : C(W,ℂ) := ⟨fun y => e y.val - e x.val,
                    (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
                  ∃ n : W → ℤ, IsLocallyConstant n ∧ ∀ x : W,
                    n x ≠ 0 ∧ ∃ v : relativeHomology W (A x) 2,
                      ∃ hpres : ∀ y ∈ A x, k x y ∈ P,
                        pairRelativeHomologyMap (A x) ({x.val}ᶜ : Set E) (ReflectionGermProof.inclusion W)
                          (fun y hy => hy) 2 v = homologyToRelative E ({x.val}ᶜ : Set E) 2 z ∧
                        n x = φ.hom (pairRelativeHomologyMap (A x) P (k x) hpres 2 v) := by
          exact actual_genus_two_complex_chart_orientation_sections M
        have chart_restrict {E : Type} [TopologicalSpace E]
            [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [MetricSpace E]
            (c : SmoothHyperbolicChart E) (U : Set E) (hU : IsOpen U) :
            ∃ d : SmoothHyperbolicChart E,
              d.chart.source = c.chart.source ∩ U ∧ ∀ x, d.chart x = c.chart x := by
          exact smooth_hyperbolic_chart_open_restriction c U hU
        have chart_reflect {E : Type} [TopologicalSpace E]
            [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [MetricSpace E]
            (c : SmoothHyperbolicChart E) :
            ∃ d : SmoothHyperbolicChart E,
              d.chart.source = c.chart.source ∧ ∀ x, d.chart x = -conj (c.chart x) := by
          exact smooth_hyperbolic_chart_reflection c
        have chart_model {E : Type} [TopologicalSpace E]
            [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [MetricSpace E]
            (c : SmoothHyperbolicChart E) :
            ∃ e : OpenPartialHomeomorph E ℂ, e.source = c.chart.source ∧
              ∀ x (hx : x ∈ c.chart.source),
                let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
                e x = D (⟨c.chart x,c.upper x hx⟩ : H2) := by
          exact actual_hyperbolic_chart_complex_plane_model c
        have overlap_transport {S : Type} [TopologicalSpace S] [T1Space S]
            (e d : OpenPartialHomeomorph S ℂ) (x : S) (he : x ∈ e.source) (hd : x ∈ d.source)
            (z : CurveComplexGenusTwo.CWHurewicz.H S 2) :
            let A : Set e.source := {y | y.val ≠ x}
            let B : Set d.source := {y | y.val ≠ x}
            let P : Set ℂ := {0}ᶜ
            let k : C(e.source,ℂ) := ⟨fun y => e y.val-e x,
              (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
            let l : C(d.source,ℂ) := ⟨fun y => d y.val-d x,
              (d.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
            ∀ (v : relativeHomology e.source A 2) (w : relativeHomology d.source B 2)
              (hk : ∀ y ∈ A, k y ∈ P) (hl : ∀ y ∈ B, l y ∈ P),
              pairRelativeHomologyMap A ({x}ᶜ : Set S) (ReflectionGermProof.inclusion e.source)
                (fun y hy => hy) 2 v = homologyToRelative S ({x}ᶜ : Set S) 2 z →
              pairRelativeHomologyMap B ({x}ᶜ : Set S) (ReflectionGermProof.inclusion d.source)
                (fun y hy => hy) 2 w = homologyToRelative S ({x}ᶜ : Set S) 2 z →
              ∀ (F : C(ℂ,ℂ)) (hF : ∀ t ∈ P, F t ∈ P),
                (∀ y ∈ e.source ∩ d.source, F (e y-e x) = d y-d x) →
                pairRelativeHomologyMap B P l hl 2 w =
                  pairRelativeHomologyMap P P F hF 2 (pairRelativeHomologyMap A P k hk 2 v) := by
          dsimp only
          intro v w hk hl hv hw F hF hcoord
          let U := e.source ∩ d.source
          let C : Set U := {y | y.val ≠ x}
          let j : C(U,e.source) := ⟨fun y => ⟨y.val,y.property.1⟩,by fun_prop⟩
          let r : C(U,d.source) := ⟨fun y => ⟨y.val,y.property.2⟩,by fun_prop⟩
          have hj : ∀ y ∈ C, j y ∈ {y : e.source | y.val ≠ x} := fun y hy => hy
          have hr : ∀ y ∈ C, r y ∈ {y : d.source | y.val ≠ x} := fun y hy => hy
          let iU := pairRelativeHomologyMap C ({x}ᶜ : Set S) (ReflectionGermProof.inclusion U)
            (fun y hy => hy) 2
          let ie := pairRelativeHomologyMap ({y : e.source | y.val ≠ x}) ({x}ᶜ : Set S)
            (ReflectionGermProof.inclusion e.source) (fun y hy => hy) 2
          let id := pairRelativeHomologyMap ({y : d.source | y.val ≠ x}) ({x}ᶜ : Set S)
            (ReflectionGermProof.inclusion d.source) (fun y hy => hy) 2
          let J := pairRelativeHomologyMap C ({y : e.source | y.val ≠ x}) j hj 2
          let R := pairRelativeHomologyMap C ({y : d.source | y.val ≠ x}) r hr 2
          haveI : IsIso iU := ReflectionGermProof.inclusion_isIso ({x}ᶜ : Set S) U
            (ReflectionGermProof.puncture_excision x U (e.open_source.inter d.open_source) ⟨he,hd⟩)
          haveI : IsIso ie := ReflectionGermProof.inclusion_isIso ({x}ᶜ : Set S) e.source
            (ReflectionGermProof.puncture_excision x e.source e.open_source he)
          haveI : IsIso id := ReflectionGermProof.inclusion_isIso ({x}ᶜ : Set S) d.source
            (ReflectionGermProof.puncture_excision x d.source d.open_source hd)
          let u := (asIso iU).inv (homologyToRelative S ({x}ᶜ : Set S) 2 z)
          have hu : iU u = homologyToRelative S ({x}ᶜ : Set S) 2 z := (asIso iU).inv_hom_id_apply _
          have hje : J ≫ ie = iU := by
            rw [←pairRelativeHomologyMap_comp]
            apply ReflectionGermProof.pairMap_congr
            apply ContinuousMap.ext
            intro y
            rfl
          have hrd : R ≫ id = iU := by
            rw [←pairRelativeHomologyMap_comp]
            apply ReflectionGermProof.pairMap_congr
            apply ContinuousMap.ext
            intro y
            rfl
          have hjv : J u = v := by
            apply (ModuleCat.mono_iff_injective ie).mp inferInstance
            change (J ≫ ie) u = ie v
            rw [hje,hu]
            exact hv.symm
          have hrw : R u = w := by
            apply (ModuleCat.mono_iff_injective id).mp inferInstance
            change (R ≫ id) u = id w
            rw [hrd,hu]
            exact hw.symm
          let k : C(e.source,ℂ) := ⟨fun y => e y.val-e x,
            (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
          let l : C(d.source,ℂ) := ⟨fun y => d y.val-d x,
            (d.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
          have hc : l.comp r = F.comp (k.comp j) := by
            apply ContinuousMap.ext
            intro y
            exact (hcoord y.val y.property).symm
          have hm : R ≫ pairRelativeHomologyMap _ _ l hl 2 =
              J ≫ pairRelativeHomologyMap _ _ k hk 2 ≫ pairRelativeHomologyMap _ _ F hF 2 := by
            rw [←pairRelativeHomologyMap_comp]
            rw [←pairRelativeHomologyMap_comp,←pairRelativeHomologyMap_comp]
            apply ReflectionGermProof.pairMap_congr
            exact hc
          rw [←hrw,←hjv]
          exact congrArg (fun t => t u) hm
        have conjugation_degree (hc : ∀ z ∈ ({0}ᶜ : Set ℂ), star z ∈ ({0}ᶜ : Set ℂ)) :
            pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ)
              ⟨star,continuous_star⟩ hc 2 = -(𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)) := by
          let P : Set ℂ := {0}ᶜ
          let Q : Set (ℝ × ℝ) := {(0,0)}ᶜ
          let e := Complex.equivRealProdCLM.toHomeomorph
          let k : C(ℂ,ℝ × ℝ) := ⟨e,e.continuous⟩
          have hk : ∀ z ∈ P, k z ∈ Q := by
            intro z hz he
            exact hz (e.injective (he.trans (map_zero Complex.equivRealProdCLM).symm))
          have hki : ∀ z ∈ Q, e.symm z ∈ P := by
            intro z hz he
            exact hz ((congrArg e he).trans (map_zero Complex.equivRealProdCLM))
          haveI : IsIso (pairRelativeHomologyMap P Q k hk 2) :=
            ReflectionGermProof.pairHomeo_isIso P Q e hk hki 2
          let c : C(ℂ,ℂ) := ⟨star,continuous_star⟩
          have heq : k.comp c = planeReflection.comp k := by
            apply ContinuousMap.ext
            intro z
            apply Prod.ext <;> rfl
          have hR : pairRelativeHomologyMap Q Q planeReflection planeReflection_preserves_puncture 2 =
              -(𝟙 (relativeHomology (ℝ × ℝ) Q 2)) := planeReflection_relativeHomologyMap_eq_neg_id
          change pairRelativeHomologyMap P P c hc 2 = -(𝟙 (relativeHomology ℂ P 2))
          apply (cancel_mono (pairRelativeHomologyMap P Q k hk 2)).1
          calc
            pairRelativeHomologyMap P P c hc 2 ≫ pairRelativeHomologyMap P Q k hk 2 =
                pairRelativeHomologyMap P Q (k.comp c) (fun z hz => hk _ (hc z hz)) 2 :=
              (pairRelativeHomologyMap_comp P P Q c k hc hk 2).symm
            _ = pairRelativeHomologyMap P Q (planeReflection.comp k)
                (fun z hz => planeReflection_preserves_puncture _ (hk z hz)) 2 :=
              ReflectionGermProof.pairMap_congr P Q _ _ _ _ heq 2
            _ = pairRelativeHomologyMap P Q k hk 2 ≫
                pairRelativeHomologyMap Q Q planeReflection planeReflection_preserves_puncture 2 :=
              pairRelativeHomologyMap_comp P Q Q k planeReflection hk planeReflection_preserves_puncture 2
            _ = (-(𝟙 (relativeHomology ℂ P 2))) ≫ pairRelativeHomologyMap P Q k hk 2 := by
              rw [hR]
              simp only [Preadditive.comp_neg,Preadditive.neg_comp,Category.comp_id,Category.id_comp]
        classical
        letI : MetricSpace E := G.metric
        letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
        obtain ⟨z,hz,hlocal,φ,hsections⟩ := orientation_sections M
        refine ⟨z,hz,φ,?_⟩
        intro x
        obtain ⟨c,hxc⟩ := G.smooth_hyperbolic x
        obtain ⟨e,hse,hmodel⟩ := chart_model c
        have hxe : x ∈ e.source := hse.symm ▸ hxc
        obtain ⟨n,hn,hcoeff⟩ := hsections e
        let px : e.source := ⟨x,hxe⟩
        let V : Set e.source := {y | n y = n px}
        let U : Set E := Subtype.val '' V
        have hU : IsOpen U := e.open_source.isOpenMap_subtype_val V (hn.isOpen_fiber (n px))
        have hxU : x ∈ U := ⟨px,rfl,rfl⟩
        have hUs : U ⊆ e.source := fun y hy => by obtain ⟨q,_,rfl⟩ := hy; exact q.property
        have hconstant (y : E) (hy : y ∈ U) : n ⟨y,hUs hy⟩ = n px := by
          obtain ⟨q,hq,rfl⟩ := hy
          exact hq
        obtain ⟨c0,hsc0,hc0⟩ := chart_restrict c U hU
        have hc0s : c0.chart.source ⊆ e.source := by
          intro y hy
          rw [hsc0] at hy
          exact hUs hy.2
        have hxc0 : x ∈ c0.chart.source := hsc0.symm ▸ ⟨hxc,hxU⟩
        have hnzero : n px ≠ 0 := (hcoeff px).1
        have hDJ (t : H2) :
            (cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm) (UpperHalfPlane.J • t) =
              star ((cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm) t) := by
          have hC : (cayleyOpen (UpperHalfPlane.J • t) : ℂ) = star (cayleyOpen t : ℂ) := by
            change (((UpperHalfPlane.J • t : H2) : ℂ)-Complex.I) /
                (((UpperHalfPlane.J • t : H2) : ℂ)+Complex.I) =
              star (((t : ℂ)-Complex.I)/((t : ℂ)+Complex.I))
            rw [UpperHalfPlane.coe_J_smul]
            simp only [Complex.star_def,map_div₀,map_sub,map_add,Complex.conj_I]
            rw [show -conj (t : ℂ)-Complex.I = -(conj (t : ℂ)+Complex.I) by ring,
              show -conj (t : ℂ)+Complex.I = -(conj (t : ℂ)-Complex.I) by ring]
            simpa only [sub_neg_eq_add,sub_eq_add_neg,neg_neg] using
              neg_div_neg_eq (conj (t : ℂ)+Complex.I) (conj (t : ℂ)-Complex.I)
          change (Real.sqrt (1-‖(cayleyOpen (UpperHalfPlane.J • t) : ℂ)‖^2))⁻¹ •
              (cayleyOpen (UpperHalfPlane.J • t) : ℂ) =
            star ((Real.sqrt (1-‖(cayleyOpen t : ℂ)‖^2))⁻¹ • (cayleyOpen t : ℂ))
          rw [hC,norm_star]
          simp only [Complex.real_smul,Complex.star_def,map_mul,Complex.conj_ofReal]
        have finish (d : SmoothHyperbolicChart E) (hds : d.chart.source = c0.chart.source)
            (negate : Bool)
            (hdcoords : ∀ y, d.chart y = if negate then -conj (c.chart y) else c.chart y)
            (hsgn : 0 < if negate then -n px else n px) :
            ∃ d : SmoothHyperbolicChart E, x ∈ d.chart.source ∧
              ∃ a : OpenPartialHomeomorph E ℂ, a.source = d.chart.source ∧
                (∀ y (hy : y ∈ d.chart.source),
                  let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
                  a y = D (⟨d.chart y,d.upper y hy⟩ : H2)) ∧
                ∀ y : a.source,
                  let A : Set a.source := {q | q.val ≠ y.val}
                  let k : C(a.source,ℂ) := ⟨fun q => a q.val-a y.val,
                    (a.continuousOn.comp_continuous continuous_subtype_val (fun q => q.property)).sub continuous_const⟩
                  ∃ v : relativeHomology a.source A 2,
                    ∃ hp : ∀ q ∈ A, k q ∈ ({0}ᶜ : Set ℂ),
                      pairRelativeHomologyMap A ({y.val}ᶜ : Set E) (ReflectionGermProof.inclusion a.source)
                        (fun q hq => hq) 2 v = homologyToRelative E ({y.val}ᶜ : Set E) 2 z ∧
                      0 < φ.hom (pairRelativeHomologyMap A ({0}ᶜ : Set ℂ) k hp 2 v) := by
          obtain ⟨a,hsa,hma⟩ := chart_model d
          have has : a.source ⊆ e.source := by intro y hy; apply hc0s; rwa [hsa,hds] at hy
          have hax : x ∈ a.source := by rw [hsa,hds]; exact hxc0
          obtain ⟨na,hna,hca⟩ := hsections a
          refine ⟨d,hds.symm ▸ hxc0,a,hsa,hma,?_⟩
          intro y
          obtain ⟨_,va,hpa,hva,hnaeq⟩ := hca y
          let ey : e.source := ⟨y.val,has y.property⟩
          obtain ⟨_,ve,hpe,hve,hneq⟩ := hcoeff ey
          refine ⟨va,hpa,hva,?_⟩
          have hyU : y.val ∈ U := by
            have hh : y.val ∈ c0.chart.source := hds ▸ (hsa ▸ y.property)
            exact (hsc0 ▸ hh).2
          have hny : n ey = n px := hconstant y.val hyU
          let F : C(ℂ,ℂ) := if negate then ⟨star,continuous_star⟩ else ContinuousMap.id ℂ
          have hF : ∀ t ∈ ({0}ᶜ : Set ℂ), F t ∈ ({0}ᶜ : Set ℂ) := by
            cases negate
            · exact fun t ht => ht
            · intro t ht hh; exact ht (star_eq_zero.mp hh)
          have hcoord : ∀ q ∈ e.source ∩ a.source,
              F (e q-e y.val) = a q-a y.val := by
            intro q hq
            have hq0 : q ∈ c.chart.source := hse ▸ hq.1
            have hy0 : y.val ∈ c.chart.source := hse ▸ ey.property
            have hqd : q ∈ d.chart.source := hsa ▸ hq.2
            have hyd : y.val ∈ d.chart.source := hsa ▸ y.property
            rw [hma q hqd,hma y.val hyd,hmodel q hq0,hmodel y.val hy0]
            cases negate
            · have hqeq : (⟨d.chart q,d.upper q hqd⟩ : H2) = ⟨c.chart q,c.upper q hq0⟩ := by
                apply UpperHalfPlane.ext; exact hdcoords q
              have hyeq : (⟨d.chart y.val,d.upper y.val hyd⟩ : H2) = ⟨c.chart y.val,c.upper y.val hy0⟩ := by
                apply UpperHalfPlane.ext; exact hdcoords y.val
              rw [hqeq,hyeq]
              rfl
            · have hqeq : (⟨d.chart q,d.upper q hqd⟩ : H2) = UpperHalfPlane.J • ⟨c.chart q,c.upper q hq0⟩ := by
                apply UpperHalfPlane.ext; rw [UpperHalfPlane.coe_J_smul]; exact hdcoords q
              have hyeq : (⟨d.chart y.val,d.upper y.val hyd⟩ : H2) = UpperHalfPlane.J • ⟨c.chart y.val,c.upper y.val hy0⟩ := by
                apply UpperHalfPlane.ext; rw [UpperHalfPlane.coe_J_smul]; exact hdcoords y.val
              rw [hqeq,hyeq,hDJ,hDJ]
              exact star_sub _ _
          have ht := overlap_transport e a y.val ey.property y.property z ve va hpe hpa hve hva F hF hcoord
          cases negate
          · have hid : pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) F hF 2 = 𝟙 _ := by
              exact pairRelativeHomologyMap_id _ 2
            rw [hid] at ht
            rw [ht]
            change 0 < φ.hom (pairRelativeHomologyMap _ _ _ hpe 2 ve)
            rw [←hneq,hny]
            exact hsgn
          · have hneg : pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) F hF 2 =
                -(𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)) := conjugation_degree hF
            rw [hneg] at ht
            have hh : φ.hom (pairRelativeHomologyMap _ _ _ hpa 2 va) =
                -φ.hom (pairRelativeHomologyMap _ _ _ hpe 2 ve) := by
              rw [ht]
              simp [ey]
            rw [hh,←hneq,hny]
            exact hsgn
        by_cases hp : 0 < n px
        · exact finish c0 rfl false (fun y => by simpa using hc0 y) hp
        · obtain ⟨d,hds,hdcoords⟩ := chart_reflect c0
          apply finish d hds true
          · intro y; rw [hdcoords y,hc0 y]; rfl
          · exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hnzero)
      have positive_overlap {S : Type} [TopologicalSpace S] [T1Space S]
          (e d : OpenPartialHomeomorph S ℂ) (x : S) (he : x ∈ e.source) (hd : x ∈ d.source)
          (g : GL (Fin 2) ℝ)
          (hcoord : ∀ y ∈ e.source ∩ d.source,
            let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
            D (g • D.symm (e y)) = d y)
          (z : CurveComplexGenusTwo.CWHurewicz.H S 2) (φ : relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ≅ ModuleCat.of ℤ ℤ) :
          let A : Set e.source := {y | y.val ≠ x}
          let B : Set d.source := {y | y.val ≠ x}
          let P : Set ℂ := {0}ᶜ
          let k : C(e.source,ℂ) := ⟨fun y => e y.val-e x,
            (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
          let l : C(d.source,ℂ) := ⟨fun y => d y.val-d x,
            (d.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
          ∀ (v : relativeHomology e.source A 2) (w : relativeHomology d.source B 2)
            (hk : ∀ y ∈ A, k y ∈ P) (hl : ∀ y ∈ B, l y ∈ P),
            pairRelativeHomologyMap A ({x}ᶜ : Set S) (ReflectionGermProof.inclusion e.source)
              (fun y hy => hy) 2 v = homologyToRelative S ({x}ᶜ : Set S) 2 z →
            pairRelativeHomologyMap B ({x}ᶜ : Set S) (ReflectionGermProof.inclusion d.source)
              (fun y hy => hy) 2 w = homologyToRelative S ({x}ᶜ : Set S) 2 z →
            0 < φ.hom (pairRelativeHomologyMap A P k hk 2 v) →
            0 < φ.hom (pairRelativeHomologyMap B P l hl 2 w) → 0 < g.val.det := by
        exact positive_chart_coefficients_force_positive_mobius_transition e d x he hd g hcoord z φ
      have actual_hyperbolic_atlas_transition (c d : SmoothHyperbolicChart E)
          (hne : (c.chart.source ∩ d.chart.source).Nonempty) :
          ∃ T : H2 ≃ᵢ H2, ∀ (x : E) (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source),
            T (⟨c.chart x,c.upper x hc⟩ : H2) = (⟨d.chart x,d.upper x hd⟩ : H2) := by
        classical
        let U : Set E := c.chart.source ∩ d.chart.source
        have hU : IsOpen U := c.chart.toOpenPartialHomeomorph.open_source.inter
          d.chart.toOpenPartialHomeomorph.open_source
        let V : Set H2 := {z | (z : ℂ) ∈ c.chart '' U}
        have hV : IsOpen V :=
          (c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU Set.inter_subset_left).preimage
            UpperHalfPlane.continuous_coe
        have hVne : V.Nonempty := by
          obtain ⟨x,hxc,hxd⟩ := hne
          exact ⟨⟨c.chart x,c.upper x hxc⟩,x,⟨hxc,hxd⟩,rfl⟩
        have preimage (z : V) : ∃ x : U, c.chart x.val = (z.val : ℂ) := by
          obtain ⟨x,hx,hcx⟩ := z.property
          exact ⟨⟨x,hx⟩,hcx⟩
        let lift : V → U := fun z => Classical.choose (preimage z)
        have hlift (z : V) : c.chart (lift z).val = (z.val : ℂ) :=
          Classical.choose_spec (preimage z)
        have hcoords (z : V) :
            (⟨c.chart (lift z).val,c.upper (lift z).val (lift z).property.1⟩ : H2) = z.val :=
          UpperHalfPlane.coe_injective (hlift z)
        let F : V → H2 := fun z =>
          ⟨d.chart (lift z).val,d.upper (lift z).val (lift z).property.2⟩
        have hF : Isometry F := Isometry.of_dist_eq (by
          intro y z
          change dist (⟨d.chart (lift y).val,_⟩ : H2)
            (⟨d.chart (lift z).val,_⟩ : H2) = dist y z
          rw [← d.metric_preserving ⟨(lift y).val,(lift y).property.2⟩
            ⟨(lift z).val,(lift z).property.2⟩,
            c.metric_preserving ⟨(lift y).val,(lift y).property.1⟩
            ⟨(lift z).val,(lift z).property.1⟩,hcoords y,hcoords z]
          rfl)
        obtain ⟨T,hT⟩ := local_plane_extension V hV hVne F hF
        refine ⟨T,?_⟩
        intro x hc hd
        let z : V := ⟨⟨c.chart x,c.upper x hc⟩,x,⟨hc,hd⟩,rfl⟩
        have hxlift : (lift z).val = x :=
          c.chart.toOpenPartialHomeomorph.injOn (lift z).property.1 hc (hlift z)
        change T z.val = (⟨d.chart x,d.upper x hd⟩ : H2)
        rw [hT z]
        apply UpperHalfPlane.coe_injective
        exact congrArg d.chart hxlift
      classical
      letI : MetricSpace E := H.metric
      letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
      obtain ⟨z,hz,φ,hcharts⟩ := positive_choices M H
      choose c hc e hse he hcoeff using hcharts
      refine ⟨z,φ,c,hc,e,hse,he,hcoeff,?_⟩
      intro a b hne
      obtain ⟨T,hT⟩ := actual_hyperbolic_atlas_transition (c a) (c b) hne
      obtain ⟨g,hg⟩ := axis_metric_isometry_gl_representation T
      refine ⟨g,?_,?_⟩
      · obtain ⟨x,hxa,hxb⟩ := hne
        have hxEA : x ∈ (e a).source := (hse a).symm ▸ hxa
        have hxEB : x ∈ (e b).source := (hse b).symm ▸ hxb
        have hcoord : ∀ y ∈ (e a).source ∩ (e b).source,
            let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
            D (g • D.symm (e a y)) = e b y := by
          intro y hy
          have hya : y ∈ (c a).chart.source := hse a ▸ hy.1
          have hyb : y ∈ (c b).chart.source := hse b ▸ hy.2
          rw [he a y hya,he b y hyb]
          let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
          change D (g • D.symm (D (⟨(c a).chart y,(c a).upper y hya⟩ : H2))) =
            D (⟨(c b).chart y,(c b).upper y hyb⟩ : H2)
          rw [D.symm_apply_apply,←hg]
          exact congrArg D (hT y hya hyb)
        obtain ⟨va,hpa,hva,hposa⟩ := hcoeff a ⟨x,hxEA⟩
        obtain ⟨vb,hpb,hvb,hposb⟩ := hcoeff b ⟨x,hxEB⟩
        exact positive_overlap (e a) (e b) x hxEA hxEB g hcoord z φ va vb hpa hpb hva hvb hposa hposb
      · intro y hya hyb
        rw [←hg]
        exact hT y hya hyb
    have actual_compatible_positive_atlas (c : E → SmoothHyperbolicChart E)
        (hc : ∀ x : E, x ∈ (c x).chart.source)
        (hpositive : ∀ a b : E, ((c a).chart.source ∩ (c b).chart.source).Nonempty →
          ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧
            ∀ x (ha : x ∈ (c a).chart.source) (hb : x ∈ (c b).chart.source),
              g • (⟨(c a).chart x,(c a).upper x ha⟩ : H2) =
                (⟨(c b).chart x,(c b).upper x hb⟩ : H2)) :
        ∃ A : ChartedSpace ℂ E,
          A.chartAt = (fun x => (c x).chart.toOpenPartialHomeomorph) ∧
          @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ∞ E _ A := by
      classical
      have transition_holomorphic (c d : SmoothHyperbolicChart E) (g : GL (Fin 2) ℝ)
          (hpos : 0 < g.val.det)
          (hcoord : ∀ x (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source),
            g • (⟨c.chart x,c.upper x hc⟩ : H2) =
              (⟨d.chart x,d.upper x hd⟩ : H2)) :
          ContDiffOn ℂ ∞ (c.chart.toOpenPartialHomeomorph.symm.trans
            d.chart.toOpenPartialHomeomorph)
              (c.chart.toOpenPartialHomeomorph.symm.trans
                d.chart.toOpenPartialHomeomorph).source := by
        let e := c.chart.toOpenPartialHomeomorph.symm.trans d.chart.toOpenPartialHomeomorph
        intro z hz
        have hc : z ∈ c.chart.target := hz.1
        have hxc : c.chart.symm z ∈ c.chart.source :=
          c.chart.toOpenPartialHomeomorph.map_target hc
        have hcz : c.chart (c.chart.symm z) = z :=
          c.chart.toOpenPartialHomeomorph.right_inv hc
        have him : 0 < z.im := hcz ▸ c.upper (c.chart.symm z) hxc
        let τ : H2 := ⟨z,him⟩
        have hs : ContDiffAt ℂ ∞ (fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : H2) : ℂ)) z := by
          exact UpperHalfPlane.contMDiffAt_iff.mp
            ((UpperHalfPlane.contMDiff_coe.comp (UpperHalfPlane.contMDiff_smul hpos)) τ)
        apply (hs.congr_of_eventuallyEq ?_).contDiffWithinAt
        filter_upwards [e.open_source.mem_nhds hz] with w hw
        have hcw : w ∈ c.chart.target := hw.1
        have hxw : c.chart.symm w ∈ c.chart.source :=
          c.chart.toOpenPartialHomeomorph.map_target hcw
        have hww : c.chart (c.chart.symm w) = w :=
          c.chart.toOpenPartialHomeomorph.right_inv hcw
        have hiw : 0 < w.im := hww ▸ c.upper (c.chart.symm w) hxw
        have hH : (⟨c.chart (c.chart.symm w),c.upper (c.chart.symm w) hxw⟩ : H2) =
            (⟨w,hiw⟩ : H2) := UpperHalfPlane.coe_injective hww
        have hh := hcoord (c.chart.symm w) hxw hw.2
        rw [hH] at hh
        change d.chart (c.chart.symm w) = ((g • UpperHalfPlane.ofComplex w : H2) : ℂ)
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hiw]
        exact congrArg UpperHalfPlane.coe hh.symm
      let A : ChartedSpace ℂ E := {
        atlas := Set.range (fun x : E => (c x).chart.toOpenPartialHomeomorph)
        chartAt := fun x => (c x).chart.toOpenPartialHomeomorph
        mem_chart_source := hc
        chart_mem_atlas := fun x => ⟨x,rfl⟩ }
      letI : ChartedSpace ℂ E := A
      refine ⟨A,rfl,?_⟩
      apply isManifold_of_contDiffOn
      intro e e' he he'
      obtain ⟨a,rfl⟩ := he
      obtain ⟨b,rfl⟩ := he'
      intro z hz
      have hz' : z ∈ ((c a).chart.toOpenPartialHomeomorph.symm.trans
          (c b).chart.toOpenPartialHomeomorph).source := hz.1
      have ha : (c a).chart.symm z ∈ (c a).chart.source :=
        (c a).chart.toOpenPartialHomeomorph.map_target hz'.1
      obtain ⟨g,hg,hcoord⟩ := hpositive a b ⟨(c a).chart.symm z,ha,hz'.2⟩
      have h := transition_holomorphic (c a) (c b) g hg hcoord
      simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
        Function.comp_def,id_eq,Set.range_id,Set.preimage_id,Set.inter_univ] using h z hz'
    
    have positive_coordinate_map_from_orientation {S : Type} [TopologicalSpace S] [T1Space S]
        (e d : OpenPartialHomeomorph S ℂ) (f : S ≃ₜ S) (x : S)
        (he : x ∈ e.source) (hd : f x ∈ d.source)
        (U : Set S) (hU : IsOpen U) (hxU : x ∈ U)
        (hUs : U ⊆ e.source) (hUt : MapsTo f U d.source)
        (g : GL (Fin 2) ℝ)
        (hcoord : ∀ y ∈ U,
          let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
          D (g • D.symm (e y)) = d (f y))
        (z : CurveComplexGenusTwo.CWHurewicz.H S 2)
        (φ : relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ≅ ModuleCat.of ℤ ℤ)
        (hp : ∀ y ∈ ({x}ᶜ : Set S), f y ∈ ({f x}ᶜ : Set S))
        (htransport : pairRelativeHomologyMap ({x}ᶜ : Set S) ({f x}ᶜ : Set S)
          ⟨f,f.continuous⟩ hp 2 (homologyToRelative S ({x}ᶜ : Set S) 2 z) =
            homologyToRelative S ({f x}ᶜ : Set S) 2 z) :
        let A : Set e.source := {y | y.val ≠ x}
        let B : Set d.source := {y | y.val ≠ f x}
        let P : Set ℂ := {0}ᶜ
        let k : C(e.source,ℂ) := ⟨fun y => e y.val-e x,
          (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
        let l : C(d.source,ℂ) := ⟨fun y => d y.val-d (f x),
          (d.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
        ∀ (v : relativeHomology e.source A 2) (w : relativeHomology d.source B 2)
          (hk : ∀ y ∈ A, k y ∈ P) (hl : ∀ y ∈ B, l y ∈ P),
          pairRelativeHomologyMap A ({x}ᶜ : Set S) (ReflectionGermProof.inclusion e.source)
            (fun y hy => hy) 2 v = homologyToRelative S ({x}ᶜ : Set S) 2 z →
          pairRelativeHomologyMap B ({f x}ᶜ : Set S) (ReflectionGermProof.inclusion d.source)
            (fun y hy => hy) 2 w = homologyToRelative S ({f x}ᶜ : Set S) 2 z →
          0 < φ.hom (pairRelativeHomologyMap A P k hk 2 v) →
          0 < φ.hom (pairRelativeHomologyMap B P l hl 2 w) → 0 < g.val.det := by
      have map_transport {S : Type} [TopologicalSpace S] [T1Space S]
          (e d : OpenPartialHomeomorph S ℂ) (f : S ≃ₜ S) (x : S)
          (he : x ∈ e.source) (hd : f x ∈ d.source)
          (U : Set S) (hU : IsOpen U) (hxU : x ∈ U)
          (hUs : U ⊆ e.source) (hUt : MapsTo f U d.source)
          (z : CurveComplexGenusTwo.CWHurewicz.H S 2)
          (hp : ∀ y ∈ ({x}ᶜ : Set S), f y ∈ ({f x}ᶜ : Set S))
          (htransport : pairRelativeHomologyMap ({x}ᶜ : Set S) ({f x}ᶜ : Set S)
            ⟨f,f.continuous⟩ hp 2 (homologyToRelative S ({x}ᶜ : Set S) 2 z) =
              homologyToRelative S ({f x}ᶜ : Set S) 2 z) :
          let A : Set e.source := {y | y.val ≠ x}
          let B : Set d.source := {y | y.val ≠ f x}
          let P : Set ℂ := {0}ᶜ
          let k : C(e.source,ℂ) := ⟨fun y => e y.val-e x,
            (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
          let l : C(d.source,ℂ) := ⟨fun y => d y.val-d (f x),
            (d.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
          ∀ (v : relativeHomology e.source A 2) (w : relativeHomology d.source B 2)
            (hk : ∀ y ∈ A, k y ∈ P) (hl : ∀ y ∈ B, l y ∈ P),
            pairRelativeHomologyMap A ({x}ᶜ : Set S) (ReflectionGermProof.inclusion e.source)
              (fun y hy => hy) 2 v = homologyToRelative S ({x}ᶜ : Set S) 2 z →
            pairRelativeHomologyMap B ({f x}ᶜ : Set S) (ReflectionGermProof.inclusion d.source)
              (fun y hy => hy) 2 w = homologyToRelative S ({f x}ᶜ : Set S) 2 z →
            ∀ (F : C(ℂ,ℂ)) (hF : ∀ t ∈ P, F t ∈ P),
              (∀ y ∈ U, F (e y-e x) = d (f y)-d (f x)) →
              pairRelativeHomologyMap B P l hl 2 w =
                pairRelativeHomologyMap P P F hF 2 (pairRelativeHomologyMap A P k hk 2 v) := by
        dsimp only
        intro v w hk hl hv hw F hF hcoord
        let C : Set U := {y | y.val ≠ x}
        let j : C(U,e.source) := ⟨fun y => ⟨y.val,hUs y.property⟩,by fun_prop⟩
        let r : C(U,d.source) := ⟨fun y => ⟨f y.val,hUt y.property⟩,by fun_prop⟩
        have hj : ∀ y ∈ C, j y ∈ {y : e.source | y.val ≠ x} := fun y hy => hy
        have hr : ∀ y ∈ C, r y ∈ {y : d.source | y.val ≠ f x} := by
          intro y hy hh
          exact hy (f.injective hh)
        let iU := pairRelativeHomologyMap C ({x}ᶜ : Set S) (ReflectionGermProof.inclusion U)
          (fun y hy => hy) 2
        let ie := pairRelativeHomologyMap ({y : e.source | y.val ≠ x}) ({x}ᶜ : Set S)
          (ReflectionGermProof.inclusion e.source) (fun y hy => hy) 2
        let id := pairRelativeHomologyMap ({y : d.source | y.val ≠ f x}) ({f x}ᶜ : Set S)
          (ReflectionGermProof.inclusion d.source) (fun y hy => hy) 2
        let J := pairRelativeHomologyMap C ({y : e.source | y.val ≠ x}) j hj 2
        let R := pairRelativeHomologyMap C ({y : d.source | y.val ≠ f x}) r hr 2
        let G := pairRelativeHomologyMap ({x}ᶜ : Set S) ({f x}ᶜ : Set S) ⟨f,f.continuous⟩ hp 2
        haveI : IsIso iU := ReflectionGermProof.inclusion_isIso ({x}ᶜ : Set S) U
          (ReflectionGermProof.puncture_excision x U hU hxU)
        haveI : IsIso ie := ReflectionGermProof.inclusion_isIso ({x}ᶜ : Set S) e.source
          (ReflectionGermProof.puncture_excision x e.source e.open_source he)
        haveI : IsIso id := ReflectionGermProof.inclusion_isIso ({f x}ᶜ : Set S) d.source
          (ReflectionGermProof.puncture_excision (f x) d.source d.open_source hd)
        let u := (asIso iU).inv (homologyToRelative S ({x}ᶜ : Set S) 2 z)
        have hu : iU u = homologyToRelative S ({x}ᶜ : Set S) 2 z := (asIso iU).inv_hom_id_apply _
        have hje : J ≫ ie = iU := by
          rw [←pairRelativeHomologyMap_comp]
          apply ReflectionGermProof.pairMap_congr
          apply ContinuousMap.ext
          intro y
          rfl
        have hrd : R ≫ id = iU ≫ G := by
          rw [←pairRelativeHomologyMap_comp,←pairRelativeHomologyMap_comp]
          apply ReflectionGermProof.pairMap_congr
          apply ContinuousMap.ext
          intro y
          rfl
        have hjv : J u = v := by
          apply (ModuleCat.mono_iff_injective ie).mp inferInstance
          change (J ≫ ie) u = ie v
          rw [hje,hu]
          exact hv.symm
        have hrw : R u = w := by
          apply (ModuleCat.mono_iff_injective id).mp inferInstance
          change (R ≫ id) u = id w
          rw [hrd]
          change G (iU u) = id w
          rw [hu,htransport]
          exact hw.symm
        let k : C(e.source,ℂ) := ⟨fun y => e y.val-e x,
          (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
        let l : C(d.source,ℂ) := ⟨fun y => d y.val-d (f x),
          (d.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
        have hc : l.comp r = F.comp (k.comp j) := by
          apply ContinuousMap.ext
          intro y
          exact (hcoord y.val y.property).symm
        have hm : R ≫ pairRelativeHomologyMap _ _ l hl 2 =
            J ≫ pairRelativeHomologyMap _ _ k hk 2 ≫ pairRelativeHomologyMap _ _ F hF 2 := by
          rw [←pairRelativeHomologyMap_comp]
          rw [←pairRelativeHomologyMap_comp,←pairRelativeHomologyMap_comp]
          apply ReflectionGermProof.pairMap_congr
          exact hc
        rw [←hrw,←hjv]
        exact congrArg (fun t => t u) hm
      have negative_degree (g : GL (Fin 2) ℝ) (hneg : g.val.det < 0) (p : ℂ)
          (f : C(ℂ,ℂ))
          (hf : ∀ z : ℂ,
            let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
            f z = D (g • D.symm (z+p)) - D (g • D.symm p))
          (hpres : ∀ z ∈ ({0}ᶜ : Set ℂ), f z ∈ ({0}ᶜ : Set ℂ)) :
          pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) f hpres 2 =
            -(𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)) := by
        exact negative_mobius_moving_center_local_top_homology g hneg p f hf hpres
      dsimp only
      intro v w hk hl hv hw ha hb
      by_contra hn
      have hneg : g.val.det < 0 := lt_of_le_of_ne (le_of_not_gt hn) g.det_ne_zero
      let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
      let F : C(ℂ,ℂ) := ⟨fun t => D (g • D.symm (t+e x))-D (g • D.symm (e x)),by fun_prop⟩
      have hF : ∀ t ∈ ({0}ᶜ : Set ℂ), F t ∈ ({0}ᶜ : Set ℂ) := by
        intro t ht hh
        apply ht
        have h := D.symm.injective (MulAction.injective g (D.injective (sub_eq_zero.mp hh)))
        exact add_right_cancel (show t+e x = (0 : ℂ)+e x by simpa only [zero_add] using h)
      have hc : ∀ y ∈ U, F (e y-e x) = d (f y)-d (f x) := by
        intro y hy
        change D (g • D.symm ((e y-e x)+e x))-D (g • D.symm (e x)) = d (f y)-d (f x)
        rw [sub_add_cancel,hcoord y hy,hcoord x hxU]
      have ht := map_transport e d f x he hd U hU hxU hUs hUt z hp htransport v w hk hl hv hw F hF hc
      have hnegative := negative_degree g hneg (e x) F (fun t => rfl) hF
      rw [hnegative] at ht
      have heq : φ.hom (pairRelativeHomologyMap _ _ _ hl 2 w) =
          -φ.hom (pairRelativeHomologyMap _ _ _ hk 2 v) := by
        rw [ht]
        simp
      rw [heq] at hb
      exact (not_lt_of_ge (neg_nonpos.mpr ha.le)) hb
    obtain ⟨coherent_z, coherent_phi, coherent_c, coherent_c_point, coherent_e,
      coherent_e_source, coherent_e_formula, coherent_coeff, coherent_c_transition⟩ :=
      actual_coherent_positive_chart_family M H
    obtain ⟨actualComplexAtlas, actualComplexAtlas_chartAt, actualComplexManifold⟩ :=
      actual_compatible_positive_atlas coherent_c coherent_c_point coherent_c_transition
    have J_transport_all_classes (q : E) (z : CurveComplexGenusTwo.CWHurewicz.H E 2) :
        ∃ hp : ∀ y ∈ ({q}ᶜ : Set E), J y ∈ ({J q}ᶜ : Set E),
          pairRelativeHomologyMap ({q}ᶜ : Set E) ({J q}ᶜ : Set E)
            ⟨J,J.continuous⟩ hp 2 (homologyToRelative E ({q}ᶜ : Set E) 2 z) =
              homologyToRelative E ({J q}ᶜ : Set E) 2 z := by
      have hp : ∀ y ∈ ({q}ᶜ : Set E), J y ∈ ({J q}ᶜ : Set E) := by
        intro y hy heq
        exact hy (J.injective heq)
      refine ⟨hp,?_⟩
      have hn := pairRelativeHomologyMap_commutes ({q}ᶜ : Set E) ({J q}ᶜ : Set E)
        (⟨J,J.continuous⟩ : C(E,E)) hp 2
      change homologyToRelative E ({q}ᶜ : Set E) 2 ≫
          pairRelativeHomologyMap ({q}ᶜ : Set E) ({J q}ᶜ : Set E)
            ⟨J,J.continuous⟩ hp 2 =
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (⟨J,J.continuous⟩ : C(E,E)))) ≫
            homologyToRelative E ({J q}ᶜ : Set E) 2 at hn
      rw [actual_J_global_orientation_identity] at hn
      exact congrArg (fun k : integralHomology E 2 ⟶
        relativeHomology E ({J q}ᶜ : Set E) 2 => k z) hn
    have J_coherent_positive_germs (q : E) :
        ∃ (U : Set E) (g : GL (Fin 2) ℝ), IsOpen U ∧ q ∈ U ∧
          ∃ hUs : U ⊆ (coherent_c q).chart.source,
          ∃ hUt : MapsTo J U (coherent_c (J q)).chart.source, 0 < g.val.det ∧
          ∀ y (hy : y ∈ U),
            g • (⟨(coherent_c q).chart y,(coherent_c q).upper y (hUs hy)⟩ : H2) =
              (⟨(coherent_c (J q)).chart (J y),(coherent_c (J q)).upper (J y) (hUt hy)⟩ : H2) := by
      obtain ⟨c,d,hqc,hJqd,W,hW,hqW,hcW,hdW,T,hT⟩ := local_chart_extension q
      obtain ⟨L,hL⟩ := actual_hyperbolic_atlas_transition (coherent_c q) c
        ⟨q,coherent_c_point q,hqc⟩
      obtain ⟨R,hR⟩ := actual_hyperbolic_atlas_transition d (coherent_c (J q))
        ⟨J q,hJqd,coherent_c_point (J q)⟩
      let U : Set E := (W ∩ (coherent_c q).chart.source) ∩ J ⁻¹' (coherent_c (J q)).chart.source
      have hU : IsOpen U := (hW.inter (coherent_c q).chart.toOpenPartialHomeomorph.open_source).inter
        ((coherent_c (J q)).chart.toOpenPartialHomeomorph.open_source.preimage J.continuous)
      have hqU : q ∈ U := ⟨⟨hqW,coherent_c_point q⟩,coherent_c_point (J q)⟩
      have hUs : U ⊆ (coherent_c q).chart.source := fun y hy => hy.1.2
      have hUt : MapsTo J U (coherent_c (J q)).chart.source := fun y hy => hy.2
      obtain ⟨g,hg⟩ := axis_metric_isometry_gl_representation ((L.trans T).trans R)
      have hcoord (y : E) (hy : y ∈ U) :
          g • (⟨(coherent_c q).chart y,(coherent_c q).upper y (hUs hy)⟩ : H2) =
            (⟨(coherent_c (J q)).chart (J y),(coherent_c (J q)).upper (J y) (hUt hy)⟩ : H2) := by
        rw [←hg,IsometryEquiv.trans_apply,IsometryEquiv.trans_apply,
          hL y (hUs hy) (hcW hy.1.1),hT ⟨y,hy.1.1⟩]
        exact hR (J y) (hdW hy.1.1) (hUt hy)
      have heq : q ∈ (coherent_e q).source := (coherent_e_source q).symm ▸ coherent_c_point q
      have heJq : J q ∈ (coherent_e (J q)).source :=
        (coherent_e_source (J q)).symm ▸ coherent_c_point (J q)
      have hUe : U ⊆ (coherent_e q).source := fun y hy => (coherent_e_source q).symm ▸ hUs hy
      have hUd : MapsTo J U (coherent_e (J q)).source :=
        fun y hy => (coherent_e_source (J q)).symm ▸ hUt hy
      have hmodel : ∀ y ∈ U,
          let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
          D (g • D.symm (coherent_e q y)) = coherent_e (J q) (J y) := by
        intro y hy
        rw [coherent_e_formula q y (hUs hy),coherent_e_formula (J q) (J y) (hUt hy)]
        let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
        change D (g • D.symm (D _)) = D _
        rw [D.symm_apply_apply,hcoord y hy]
      obtain ⟨v,hv,hvl,hvp⟩ := coherent_coeff q ⟨q,heq⟩
      obtain ⟨w,hw,hwl,hwp⟩ := coherent_coeff (J q) ⟨J q,heJq⟩
      obtain ⟨hp,htransport⟩ := J_transport_all_classes q coherent_z
      have hpos := positive_coordinate_map_from_orientation (coherent_e q) (coherent_e (J q))
        J q heq heJq U hU hqU hUe hUd g hmodel coherent_z coherent_phi hp htransport
        v w hv hw hvl hwl hvp hwp
      exact ⟨U,g,hU,hqU,hUs,hUt,hpos,hcoord⟩
    letI : ChartedSpace ℂ E := actualComplexAtlas
    haveI : IsManifold 𝓘(ℂ) ∞ E := actualComplexManifold
    have J_actual_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ J := by
      apply positive_mobius_germs_holomorphic_map (⟨J,J.continuous⟩ : C(E,E))
      intro q
      obtain ⟨U,g,hU,hqU,hUs,hUt,hpos,hcoord⟩ := J_coherent_positive_germs q
      have hchart (a : E) : chartAt ℂ a = (coherent_c a).chart.toOpenPartialHomeomorph :=
        congrFun actualComplexAtlas_chartAt a
      refine ⟨U,g,hU,hqU,?_,?_,hpos,?_⟩
      · rw [hchart q]
        exact hUs
      · change MapsTo J U (chartAt ℂ (J q)).source
        rw [hchart (J q)]
        exact hUt
      · intro y hy
        have hiy : 0 < (chartAt ℂ q y).im := by
          rw [hchart q]
          exact (coherent_c q).upper y (hUs hy)
        refine ⟨hiy,?_⟩
        change ((g • (⟨chartAt ℂ q y,hiy⟩ : H2) : H2) : ℂ) = chartAt ℂ (J q) (J y)
        have hs : (⟨chartAt ℂ q y,hiy⟩ : H2) =
            (⟨(coherent_c q).chart y,(coherent_c q).upper y (hUs hy)⟩ : H2) :=
          UpperHalfPlane.coe_injective (congrArg (fun e : OpenPartialHomeomorph E ℂ => e y) (hchart q))
        rw [hs,hchart (J q)]
        exact congrArg UpperHalfPlane.coe (hcoord y hy)
    have actual_deck_global_orientation (M : HyperellipticModel E S) :
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (⟨M.cover.deck,M.cover.deck.continuous⟩ : C(E,E)))) =
            𝟙 (integralHomology E 2) := by
      classical
      letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
      letI : T2Space E := (Classical.choice M.genusTwo.2.1).toT2Space
      have deck_six_fixed (q : BranchedDoubleCover E S) :
          ∃ F : Finset E, (F : Set E) = {x : E | q.deck x = x} ∧ F.card = 6 := by
        classical
        let lift : {b : S // b ∈ q.branch} → E :=
          fun b => Classical.choose (q.branch_fiber_unique b.property)
        have hlift (b : {b : S // b ∈ q.branch}) : q.projection (lift b) = b :=
          (Classical.choose_spec (q.branch_fiber_unique b.property)).1
        have hinj : Function.Injective lift := by
          intro b c heq
          apply Subtype.ext
          exact (hlift b).symm.trans ((congrArg q.projection heq).trans (hlift c))
        refine ⟨q.branch.attach.image lift, ?_, ?_⟩
        · ext x
          change x ∈ q.branch.attach.image lift ↔ q.deck x = x
          constructor
          · intro hx
            obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
            apply (q.fixed_iff_branch (lift b)).2
            simpa only [hlift] using b.property
          · intro hx
            have hb : q.projection x ∈ q.branch := (q.fixed_iff_branch x).1 hx
            let b : {b : S // b ∈ q.branch} := ⟨q.projection x, hb⟩
            apply Finset.mem_image.mpr
            refine ⟨b, Finset.mem_attach _ _, ?_⟩
            exact ((Classical.choose_spec (q.branch_fiber_unique b.property)).2 x rfl).symm
        · rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
          exact q.branch_card
      obtain ⟨F,hF,hcard⟩ := deck_six_fixed M.cover
      obtain ⟨x,hxF⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
      have hx : M.cover.deck x = x := by
        have hh : x ∈ (F : Set E) := hxF
        rw [hF] at hh
        exact hh
      let B : Set E := (F : Set E) \ {x}
      have hBclosed : IsClosed B := (F.finite_toSet.subset Set.sdiff_subset).isClosed
      have hxB : x ∈ Bᶜ := by simp [B]
      let c := M.cover.branch_chart x ((M.cover.fixed_iff_branch x).mp hx)
      let e : OpenPartialHomeomorph E (ℝ × ℝ) :=
        c.upstairs.transHomeomorph Complex.equivRealProdCLM.toHomeomorph
      have heS : e.source = c.upstairs.source := rfl
      have hex : e x = 0 := by
        change Complex.equivRealProdCLM (c.upstairs x) = 0
        rw [c.upstairs_center,map_zero]
      let U : Set E := (c.upstairs.source ∩ M.cover.deck ⁻¹' c.upstairs.source) ∩ Bᶜ
      have hU : IsOpen U := (c.upstairs.open_source.inter
        (c.upstairs.open_source.preimage M.cover.deck.continuous)).inter hBclosed.isOpen_compl
      have hxU : x ∈ U := ⟨⟨c.upstairs_mem,by change M.cover.deck x ∈ c.upstairs.source; rw [hx]; exact c.upstairs_mem⟩,hxB⟩
      have hUs : U ⊆ e.source := fun y hy => hy.1.1
      have hcoord (y : E) (hy : y ∈ U) : e (M.cover.deck y) = -e y := by
        have hsq : c.upstairs (M.cover.deck y) ^ 2 = c.upstairs y ^ 2 := by
          rw [←c.square _ hy.1.2,←c.square _ hy.1.1,M.cover.projection_deck]
        have hneg : c.upstairs (M.cover.deck y) = -c.upstairs y := by
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
          · have hyfix : M.cover.deck y = y := c.upstairs.injOn hy.1.2 hy.1.1 heq
            have hyF : y ∈ (F : Set E) := by rw [hF]; exact hyfix
            have hyx : y = x := by
              by_contra hn
              exact hy.2 ⟨hyF,by simpa using hn⟩
            rw [hyx,hx,c.upstairs_center,neg_zero]
          · exact heq
        change Complex.equivRealProdCLM (c.upstairs (M.cover.deck y)) =
          -Complex.equivRealProdCLM (c.upstairs y)
        rw [hneg,map_neg]
      have hImage : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU hUs
      have h0 : (0 : ℝ × ℝ) ∈ e '' U := ⟨x,hxU,hex⟩
      obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp hImage 0 h0
      let r : ℝ := δ / 2
      have hr : 0 < r := by dsimp [r]; linarith
      have hclosed : Metric.closedBall (0 : ℝ × ℝ) r ⊆ e.target := by
        intro z hz
        have hzδ : z ∈ Metric.ball (0 : ℝ × ℝ) δ :=
          Metric.closedBall_subset_ball (by dsimp [r]; linarith) hz
        obtain ⟨y,hy,he⟩ := hδU hzδ
        exact he ▸ e.map_source (hUs hy)
      have hgerm : ∀ z ∈ Metric.ball (0 : ℝ × ℝ) r,
          M.cover.deck (e.symm z) = e.symm (-z) := by
        intro z hz
        have hzr : z ∈ e.target := hclosed (Metric.ball_subset_closedBall hz)
        have hnzr : -z ∈ e.target := hclosed (by simpa using Metric.ball_subset_closedBall hz)
        obtain ⟨y,hy,hey⟩ := hδU (Metric.ball_subset_ball (by dsimp [r]; linarith) hz)
        have hys : e.symm z = y := hey ▸ e.left_inv (hUs hy)
        rw [hys]
        apply e.injOn hy.1.2 (e.map_target hnzr)
        rw [hcoord y hy,e.right_inv hnzr,hey]
      have hp : ∀ y ∈ ({x}ᶜ : Set E), M.cover.deck y ∈ ({x}ᶜ : Set E) := by
        intro y hy hh
        exact hy (M.cover.deck.injective (hh.trans hx.symm))
      apply actual_global_orientation_from_one_germ M M.cover.deck x hp
      exact chart_central_inversion_local_homology_identity E x e c.upstairs_mem hex
        ⟨M.cover.deck,M.cover.deck.continuous⟩ hp r hr hclosed hgerm
    have positive_local_isometry_holomorphic (f : E ≃ₜ E)
        (hlocal : ∀ q : E, ∃ U : Set E, IsOpen U ∧ q ∈ U ∧
          ∀ y ∈ U, ∀ z ∈ U, dist (f y) (f z) = dist y z)
        (hglobal : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (⟨f,f.continuous⟩ : C(E,E)))) =
            𝟙 (integralHomology E 2)) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f := by
      have f_transport_all_classes (q : E) (z : CurveComplexGenusTwo.CWHurewicz.H E 2) :
          ∃ hp : ∀ y ∈ ({q}ᶜ : Set E), f y ∈ ({f q}ᶜ : Set E),
            pairRelativeHomologyMap ({q}ᶜ : Set E) ({f q}ᶜ : Set E)
              ⟨f,f.continuous⟩ hp 2 (homologyToRelative E ({q}ᶜ : Set E) 2 z) =
                homologyToRelative E ({f q}ᶜ : Set E) 2 z := by
        have hp : ∀ y ∈ ({q}ᶜ : Set E), f y ∈ ({f q}ᶜ : Set E) := by
          intro y hy heq
          exact hy (f.injective heq)
        refine ⟨hp,?_⟩
        have hn := pairRelativeHomologyMap_commutes ({q}ᶜ : Set E) ({f q}ᶜ : Set E)
          (⟨f,f.continuous⟩ : C(E,E)) hp 2
        change homologyToRelative E ({q}ᶜ : Set E) 2 ≫
            pairRelativeHomologyMap ({q}ᶜ : Set E) ({f q}ᶜ : Set E)
              ⟨f,f.continuous⟩ hp 2 =
          (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (⟨f,f.continuous⟩ : C(E,E)))) ≫
              homologyToRelative E ({f q}ᶜ : Set E) 2 at hn
        rw [hglobal] at hn
        exact congrArg (fun k : integralHomology E 2 ⟶
          relativeHomology E ({f q}ᶜ : Set E) 2 => k z) hn
      have f_coherent_positive_germs (q : E) :
          ∃ (U : Set E) (g : GL (Fin 2) ℝ), IsOpen U ∧ q ∈ U ∧
            ∃ hUs : U ⊆ (coherent_c q).chart.source,
            ∃ hUt : MapsTo f U (coherent_c (f q)).chart.source, 0 < g.val.det ∧
            ∀ y (hy : y ∈ U),
              g • (⟨(coherent_c q).chart y,(coherent_c q).upper y (hUs hy)⟩ : H2) =
                (⟨(coherent_c (f q)).chart (f y),(coherent_c (f q)).upper (f y) (hUt hy)⟩ : H2) := by
        let c := coherent_c q
        let d := coherent_c (f q)
        obtain ⟨W,hW,hqW,hdist⟩ := hlocal q
        let U : Set E := (W ∩ c.chart.source) ∩ f ⁻¹' d.chart.source
        have hU : IsOpen U := (hW.inter c.chart.toOpenPartialHomeomorph.open_source).inter
          (d.chart.toOpenPartialHomeomorph.open_source.preimage f.continuous)
        have hqU : q ∈ U := ⟨⟨hqW,coherent_c_point q⟩,coherent_c_point (f q)⟩
        have hUs : U ⊆ c.chart.source := fun y hy => hy.1.2
        have hUt : MapsTo f U d.chart.source := fun y hy => hy.2
        let V : Set H2 := {z | (z : ℂ) ∈ c.chart '' U}
        have hV : IsOpen V :=
          (c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source hU hUs).preimage
            UpperHalfPlane.continuous_coe
        have hVne : V.Nonempty := ⟨⟨c.chart q,c.upper q (hUs hqU)⟩,q,hqU,rfl⟩
        have preimage (z : V) : ∃ y : U, c.chart y.val = (z.val : ℂ) := by
          obtain ⟨y,hy,hcy⟩ := z.property
          exact ⟨⟨y,hy⟩,hcy⟩
        let lift : V → U := fun z => Classical.choose (preimage z)
        have hlift (z : V) : c.chart (lift z).val = (z.val : ℂ) := Classical.choose_spec (preimage z)
        have hcoords (z : V) :
            (⟨c.chart (lift z).val,c.upper (lift z).val (hUs (lift z).property)⟩ : H2) = z.val :=
          UpperHalfPlane.coe_injective (hlift z)
        let F : V → H2 := fun z =>
          ⟨d.chart (f (lift z).val),d.upper (f (lift z).val) (hUt (lift z).property)⟩
        have hF : Isometry F := Isometry.of_dist_eq (by
          intro y z
          calc
            dist (F y) (F z) = dist (f (lift y).val) (f (lift z).val) :=
              (d.metric_preserving ⟨f (lift y).val,hUt (lift y).property⟩
                ⟨f (lift z).val,hUt (lift z).property⟩).symm
            _ = dist (lift y).val (lift z).val :=
              hdist _ (lift y).property.1.1 _ (lift z).property.1.1
            _ = dist y z := by
              rw [c.metric_preserving ⟨(lift y).val,hUs (lift y).property⟩
                ⟨(lift z).val,hUs (lift z).property⟩,hcoords y,hcoords z]
              rfl)
        obtain ⟨T,hT⟩ := local_plane_extension V hV hVne F hF
        obtain ⟨g,hg⟩ := axis_metric_isometry_gl_representation T
        have hcoord (y : E) (hy : y ∈ U) :
            g • (⟨c.chart y,c.upper y (hUs hy)⟩ : H2) =
              (⟨d.chart (f y),d.upper (f y) (hUt hy)⟩ : H2) := by
          let v : V := ⟨⟨c.chart y,c.upper y (hUs hy)⟩,y,hy,rfl⟩
          have hylift : (lift v).val = y :=
            c.chart.toOpenPartialHomeomorph.injOn (hUs (lift v).property) (hUs hy) (hlift v)
          rw [←hg]
          change T v.val = _
          rw [hT v]
          apply UpperHalfPlane.coe_injective
          exact congrArg (fun t => d.chart (f t)) hylift
        have heq : q ∈ (coherent_e q).source := (coherent_e_source q).symm ▸ coherent_c_point q
        have heJq : f q ∈ (coherent_e (f q)).source :=
          (coherent_e_source (f q)).symm ▸ coherent_c_point (f q)
        have hUe : U ⊆ (coherent_e q).source := fun y hy => (coherent_e_source q).symm ▸ hUs hy
        have hUd : MapsTo f U (coherent_e (f q)).source :=
          fun y hy => (coherent_e_source (f q)).symm ▸ hUt hy
        have hmodel : ∀ y ∈ U,
            let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
            D (g • D.symm (coherent_e q y)) = coherent_e (f q) (f y) := by
          intro y hy
          rw [coherent_e_formula q y (hUs hy),coherent_e_formula (f q) (f y) (hUt hy)]
          let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
          change D (g • D.symm (D _)) = D _
          rw [D.symm_apply_apply,hcoord y hy]
        obtain ⟨v,hv,hvl,hvp⟩ := coherent_coeff q ⟨q,heq⟩
        obtain ⟨w,hw,hwl,hwp⟩ := coherent_coeff (f q) ⟨f q,heJq⟩
        obtain ⟨hp,htransport⟩ := f_transport_all_classes q coherent_z
        have hpos := positive_coordinate_map_from_orientation (coherent_e q) (coherent_e (f q))
          f q heq heJq U hU hqU hUe hUd g hmodel coherent_z coherent_phi hp htransport
          v w hv hw hvl hwl hvp hwp
        exact ⟨U,g,hU,hqU,hUs,hUt,hpos,hcoord⟩

      apply positive_mobius_germs_holomorphic_map (⟨f,f.continuous⟩ : C(E,E))
      intro q
      obtain ⟨U,g,hU,hqU,hUs,hUt,hpos,hcoord⟩ := f_coherent_positive_germs q
      have hchart (a : E) : chartAt ℂ a = (coherent_c a).chart.toOpenPartialHomeomorph :=
        congrFun actualComplexAtlas_chartAt a
      refine ⟨U,g,hU,hqU,?_,?_,hpos,?_⟩
      · rw [hchart q]
        exact hUs
      · change MapsTo f U (chartAt ℂ (f q)).source
        rw [hchart (f q)]
        exact hUt
      · intro y hy
        have hiy : 0 < (chartAt ℂ q y).im := by
          rw [hchart q]
          exact (coherent_c q).upper y (hUs hy)
        refine ⟨hiy,?_⟩
        change ((g • (⟨chartAt ℂ q y,hiy⟩ : H2) : H2) : ℂ) = chartAt ℂ (f q) (f y)
        have hs : (⟨chartAt ℂ q y,hiy⟩ : H2) =
            (⟨(coherent_c q).chart y,(coherent_c q).upper y (hUs hy)⟩ : H2) :=
          UpperHalfPlane.coe_injective (congrArg (fun e : OpenPartialHomeomorph E ℂ => e y) (hchart q))
        rw [hs,hchart (f q)]
        exact congrArg UpperHalfPlane.coe (hcoord y hy)
    have deck_actual_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ M.cover.deck := by
      apply positive_local_isometry_holomorphic M.cover.deck
      · intro q
        exact ⟨Set.univ,isOpen_univ,Set.mem_univ q,fun y hy z hz => hdeck.dist_eq y z⟩
      · exact actual_deck_global_orientation M
    have actual_deck_six_fixed (q : BranchedDoubleCover E S) :
        ∃ F : Finset E, (F : Set E) = {x : E | q.deck x = x} ∧ F.card = 6 := by
      classical
      let lift : {b : S // b ∈ q.branch} → E :=
        fun b => Classical.choose (q.branch_fiber_unique b.property)
      have hlift (b : {b : S // b ∈ q.branch}) : q.projection (lift b) = b :=
        (Classical.choose_spec (q.branch_fiber_unique b.property)).1
      have hinj : Function.Injective lift := by
        intro b c heq
        apply Subtype.ext
        exact (hlift b).symm.trans ((congrArg q.projection heq).trans (hlift c))
      refine ⟨q.branch.attach.image lift, ?_, ?_⟩
      · ext x
        change x ∈ q.branch.attach.image lift ↔ q.deck x = x
        constructor
        · intro hx
          obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
          apply (q.fixed_iff_branch (lift b)).2
          simpa only [hlift] using b.property
        · intro hx
          have hb : q.projection x ∈ q.branch := (q.fixed_iff_branch x).1 hx
          let b : {b : S // b ∈ q.branch} := ⟨q.projection x, hb⟩
          apply Finset.mem_image.mpr
          refine ⟨b, Finset.mem_attach _ _, ?_⟩
          exact ((Classical.choose_spec (q.branch_fiber_unique b.property)).2 x rfl).symm
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
        exact q.branch_card
    have actual_deck_involutive : Function.Involutive M.cover.deck := M.cover.deck_involution
    have actual_deck_full_fixed_set := actual_deck_six_fixed M.cover
    have actual_quotient_regular_chart {B : Type} [TopologicalSpace B]
    (f : E ≃ₜ E) (p : E → B) (hp : IsOpenQuotientMap p)
    (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = f x) :
    IsLocalHomeomorphOn p {x | f x ≠ x} := by
      intro x hx
      obtain ⟨V, W, hV, hW, hxV, hfxW, hVW⟩ := t2_separation hx.symm
      let U := V ∩ f ⁻¹' W
      have hU : IsOpen U := hV.inter (hW.preimage f.continuous)
      have hxU : x ∈ U := ⟨hxV, hfxW⟩
      have hinj : Set.InjOn p U := by
        intro y hy z hz hyz
        rcases (hfiber z y).mp hyz with heq | heq
        · exact heq
        · exfalso
          have hyW : y ∈ W := heq ▸ hz.2
          exact Set.disjoint_left.mp hVW hy.1 hyW
      letI : Nonempty E := ⟨x⟩
      exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict hinj.toPartialEquiv
        hp.continuous.continuousOn
        (hp.isOpenMap.comp hU.isOpenEmbedding_subtypeVal.isOpenMap) hU, hxU, rfl⟩
    have actual_J_quotient_with_regular_charts :
        ∃ (B : Type) (t : TopologicalSpace B) (p : E → B),
          letI : TopologicalSpace B := t
          T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
          IsOpenQuotientMap p ∧ (∀ x y, p y = p x ↔ y = x ∨ y = J x) ∧
          (∀ x, p ⁻¹' {p x} = {x, J x}) ∧
          IsLocalHomeomorphOn p {x | J x ≠ x} := by
      obtain ⟨B, t, p, ht, hc, hconn, hp, hfiber, hpair⟩ :=
        actual_involution_compact_hausdorff_quotient J hJinv
      letI : TopologicalSpace B := t
      exact ⟨B, t, p, ht, hc, hconn, hp, hfiber, hpair,
        actual_quotient_regular_chart J p hp hfiber⟩
    have actual_deck_quotient_with_regular_charts :
        ∃ (B : Type) (t : TopologicalSpace B) (p : E → B),
          letI : TopologicalSpace B := t
          T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
          IsOpenQuotientMap p ∧ (∀ x y, p y = p x ↔ y = x ∨ y = M.cover.deck x) ∧
          (∀ x, p ⁻¹' {p x} = {x, M.cover.deck x}) ∧
          IsLocalHomeomorphOn p {x | M.cover.deck x ≠ x} := by
      obtain ⟨B, t, p, ht, hc, hconn, hp, hfiber, hpair⟩ :=
        actual_involution_compact_hausdorff_quotient M.cover.deck actual_deck_involutive
      letI : TopologicalSpace B := t
      exact ⟨B, t, p, ht, hc, hconn, hp, hfiber, hpair,
        actual_quotient_regular_chart M.cover.deck p hp hfiber⟩
    have actual_six_quotient_branch_values {B : Type} (f : E → E) (p : E → B)
    (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = f x)
    (F : Finset E) (hfix : (F : Set E) = {x | f x = x}) (hcard : F.card = 6) :
    ∃ D : Finset B, D.card = 6 ∧ (D : Set B) = p '' {x | f x = x} ∧
      (∀ x, p x ∈ D ↔ f x = x) ∧
      (∀ x, f x = x → p ⁻¹' {p x} = {x}) ∧
      (∀ x, f x ≠ x → (p ⁻¹' {p x}).Finite ∧ (p ⁻¹' {p x}).ncard = 2) := by
      classical
      have hinj : Set.InjOn p (F : Set E) := by
        intro x hx y hy hxy
        have hyfix : f y = y := by rw [hfix] at hy; exact hy
        rcases (hfiber y x).mp hxy with h | h
        · exact h
        · exact h.trans hyfix
      refine ⟨F.image p, (Finset.card_image_of_injOn hinj).trans hcard, ?_, ?_, ?_, ?_⟩
      · rw [Finset.coe_image, hfix]
      · intro x
        constructor
        · intro hx
          obtain ⟨y, hy, hpx⟩ := Finset.mem_image.mp hx
          have hyfix : f y = y := by have hh : y ∈ (F : Set E) := hy; rw [hfix] at hh; exact hh
          have hxy : x = y := by
            rcases (hfiber y x).mp hpx.symm with h | h
            · exact h
            · exact h.trans hyfix
          simpa [hxy] using hyfix
        · intro hx
          have hh : x ∈ (F : Set E) := by
            rw [hfix]
            exact hx
          exact Finset.mem_image.mpr ⟨x, hh, rfl⟩
      · intro x hx
        ext y
        simp only [mem_preimage, mem_singleton_iff, hfiber x y, hx, or_self]
      · intro x hx
        have he : p ⁻¹' {p x} = {x, f x} := by ext y; exact hfiber x y
        rw [he]
        exact ⟨Set.toFinite _, Set.ncard_pair hx.symm⟩
    have actual_J_six_branch_quotient :
        ∃ (B : Type) (t : TopologicalSpace B) (p : E → B),
          letI : TopologicalSpace B := t
          T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
          IsOpenQuotientMap p ∧ (∀ x y, p y = p x ↔ y = x ∨ y = J x) ∧
          IsLocalHomeomorphOn p {x | J x ≠ x} ∧
          ∃ D : Finset B, D.card = 6 ∧ (D : Set B) = p '' {x | J x = x} ∧
          (∀ x, p x ∈ D ↔ J x = x) ∧
          (∀ x, J x = x → p ⁻¹' {p x} = {x}) ∧
          (∀ x, J x ≠ x → (p ⁻¹' {p x}).Finite ∧ (p ⁻¹' {p x}).ncard = 2) := by
      obtain ⟨B,t,p,ht,hc,hconn,hp,hfiber,hpair,hreg⟩ := actual_J_quotient_with_regular_charts
      letI : TopologicalSpace B := t
      obtain ⟨F,hF,hcard⟩ := hfix
      exact ⟨B,t,p,ht,hc,hconn,hp,hfiber,hreg,
        actual_six_quotient_branch_values J p hfiber F hF hcard⟩
    have actual_deck_six_branch_quotient :
        ∃ (B : Type) (t : TopologicalSpace B) (p : E → B),
          letI : TopologicalSpace B := t
          T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
          IsOpenQuotientMap p ∧ (∀ x y, p y = p x ↔ y = x ∨ y = M.cover.deck x) ∧
          IsLocalHomeomorphOn p {x | M.cover.deck x ≠ x} ∧
          ∃ D : Finset B, D.card = 6 ∧ (D : Set B) = p '' {x | M.cover.deck x = x} ∧
          (∀ x, p x ∈ D ↔ M.cover.deck x = x) ∧
          (∀ x, M.cover.deck x = x → p ⁻¹' {p x} = {x}) ∧
          (∀ x, M.cover.deck x ≠ x → (p ⁻¹' {p x}).Finite ∧ (p ⁻¹' {p x}).ncard = 2) := by
      obtain ⟨B,t,p,ht,hc,hconn,hp,hfiber,hpair,hreg⟩ := actual_deck_quotient_with_regular_charts
      letI : TopologicalSpace B := t
      obtain ⟨F,hF,hcard⟩ := actual_deck_full_fixed_set
      exact ⟨B,t,p,ht,hc,hconn,hp,hfiber,hreg,
        actual_six_quotient_branch_values M.cover.deck p hfiber F hF hcard⟩
    have actual_fixed_quotient_square_chart {B : Type} [TopologicalSpace B]
    (f : E ≃ₜ E) (hinv : Function.Involutive f)
    (hfinite : {x : E | f x = x}.Finite)
    (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f)
    (p : E → B) (hp : IsOpenQuotientMap p)
    (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = f x)
    (q : E) (hfix : f q = q) :
    ∃ (e : OpenPartialHomeomorph E ℂ) (U : Set E)
      (c : OpenPartialHomeomorph B ℂ),
      IsOpen U ∧ q ∈ U ∧ U ⊆ e.source ∧ e q = 0 ∧
      Set.MapsTo f U U ∧
      (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x) ∧
      (∀ w ∈ e '' U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w) ∧
      c.source = p '' U ∧ p q ∈ c.source ∧
      c.target = (fun z : ℂ => z ^ 2) '' (e '' U) ∧
      (∀ x ∈ U, c (p x) = (e x) ^ 2) := by
      have hnormal :
        ∃ (e : OpenPartialHomeomorph E ℂ) (U : Set E),
          IsOpen U ∧ q ∈ U ∧ U ⊆ e.source ∧ e q = 0 ∧
          Set.MapsTo f U U ∧
          (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x) ∧
          (∀ w ∈ e '' U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w) ∧
          (∀ x ∈ U, e (f x) = -e x) ∧
          (∀ x ∈ U, ∀ y ∈ U,
            (e y) ^ 2 = (e x) ^ 2 ↔ y = x ∨ y = f x) := by
        let c := chartAt ℂ q
        have hq : q ∈ c.source := mem_chart_source ℂ q
        have hhol : ContDiffAt ℂ 1 (fun w => c (f (c.symm w))) (c q) := by
          have hf := (contMDiffAt_iff_of_mem_source
            («I» := 𝓘(ℂ)) («I'» := 𝓘(ℂ)) (n := ∞)
            (x := q) (y := q) (mem_chart_source ℂ q)
            (hfix.symm ▸ mem_chart_source ℂ q)).mp (hmap q)
          have hc := hf.2
          simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ, Function.comp_def]
            using hc.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)
        let G : ℂ → ℂ := fun w => c (f (c.symm w))
        have hGfix : G (c q) = c q := by simp [G, c.left_inv hq, hfix]
        have ht : Filter.Tendsto c.symm (𝓝 (c q)) (𝓝 q) := by
          simpa only [c.left_inv hq] using
            (c.symm.continuousAt (c.map_source hq)).tendsto
        have hsource : ∀ᶠ w in 𝓝 (c q), c.symm w ∈ c.source :=
          ht.eventually (c.open_source.mem_nhds hq)
        have hfsource : ∀ᶠ w in 𝓝 (c q), f (c.symm w) ∈ c.source := by
          have hfq : Filter.Tendsto f (𝓝 q) (𝓝 q) := by
            simpa [hfix] using (f.continuous.continuousAt (x := q)).tendsto
          exact (hfq.comp ht).eventually (c.open_source.mem_nhds hq)
        have htarget : ∀ᶠ w in 𝓝 (c q), w ∈ c.target :=
          c.open_target.mem_nhds (c.map_source hq)
        have hGinv : ∀ᶠ w in 𝓝 (c q), G (G w) = w := by
          filter_upwards [hfsource, htarget] with w hw ht
          dsimp [G]
          rw [c.left_inv hw, hinv, c.right_inv ht]
        have hqnot : q ∉ ({x : E | f x = x} \ {q}) := by simp
        have haven : ∀ᶠ w in 𝓝 (c q),
            c.symm w ∉ ({x : E | f x = x} \ {q}) :=
          ht.eventually ((hfinite.diff (t := {q})).isClosed.isOpen_compl.mem_nhds hqnot)
        have hisolated : ∀ᶠ w in 𝓝[≠] (c q), G w ≠ w := by
          have hmem : ∀ᶠ w in 𝓝[≠] (c q), w ≠ c q := self_mem_nhdsWithin
          filter_upwards [hsource.filter_mono nhdsWithin_le_nhds,
            hfsource.filter_mono nhdsWithin_le_nhds,
            htarget.filter_mono nhdsWithin_le_nhds,
            haven.filter_mono nhdsWithin_le_nhds,hmem] with w hs hfs htg hav hn
          intro heq
          have hfx : f (c.symm w) = c.symm w :=
            c.injOn hfs hs (by change G w = c (c.symm w); rw [c.right_inv htg]; exact heq)
          have hxq : c.symm w = q := by
            by_contra hne
            exact hav ⟨hfx,hne⟩
          exact hn (by rw [← c.right_inv htg, hxq])
        have hd := hhol.hasStrictDerivAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
        have hminus : deriv G (c q) = -1 :=
          isolated_involution_strict_derivative_negative G (c q) _ hGfix hGinv hisolated hd
        have hdneg : HasStrictDerivAt G (-1) (c q) := hd.congr_deriv hminus
        obtain ⟨d,hdsource,hdzero,hdhol,hdinv,hdneg,hdsquare⟩ :=
          holomorphic_involution_biholomorphic_branch_coordinate G (c q) hGfix hGinv hdneg hhol
        let e := c.trans d
        have hzero : e q = 0 := hdzero
        have hesource : q ∈ e.source := ⟨hq,hdsource⟩
        have hcchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 c q :=
          (contMDiffAt_of_mem_maximalAtlas («I» := 𝓘(ℂ))
            (n := ∞) (IsManifold.chart_mem_maximalAtlas q) hq).of_le (by simp)
        have hehol : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e q :=
          hdhol.self_of_nhds.contMDiffAt.comp q hcchart
        have hcchartinv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 c.symm (c q) :=
          (contMDiffAt_symm_of_mem_maximalAtlas («I» := 𝓘(ℂ))
            (n := ∞) (IsManifold.chart_mem_maximalAtlas q) (c.map_source hq)).of_le (by simp)
        have hdinvzero : d.symm 0 = c q := by
          rw [← hdzero,d.left_inv hdsource]
        have heinv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm 0 := by
          have h := (hdinvzero.symm ▸ hcchartinv).comp (0 : ℂ)
            hdinv.self_of_nhds.contMDiffAt
          exact h
        have htc : Filter.Tendsto c (𝓝 q) (𝓝 (c q)) := (c.continuousAt hq).tendsto
        have heneg : ∀ᶠ x in 𝓝 q, e (f x) = -e x := by
          filter_upwards [htc.eventually hdneg,c.open_source.mem_nhds hq] with x hx hxs
          change d (c (f (c.symm (c x)))) = -d (c x) at hx
          rw [c.left_inv hxs] at hx
          exact hx
        have hmapnear : ∀ᶠ x in 𝓝 q, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x :=
          (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hehol
        have hinvnear : ∀ᶠ w in 𝓝 (0 : ℂ), ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w :=
          (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp heinv
        have hemap : Filter.Tendsto e (𝓝 q) (𝓝 (0 : ℂ)) := by
          simpa [hzero] using (e.continuousAt hesource).tendsto
        have hall : ∀ᶠ x in 𝓝 q, x ∈ e.source ∧
            ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x ∧
            ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm (e x) ∧ e (f x) = -e x := by
          filter_upwards [e.open_source.mem_nhds hesource,hmapnear,
            hemap.eventually hinvnear,heneg] with x hs hm hi hn
          exact ⟨hs,hm,hi,hn⟩
        obtain ⟨O,hOsub,hOopen,hqO⟩ := eventually_nhds_iff.mp hall
        let U := O ∩ f ⁻¹' O
        have hU : IsOpen U := hOopen.inter (hOopen.preimage f.continuous)
        have hqU : q ∈ U := ⟨hqO,by change f q ∈ O; rw [hfix]; exact hqO⟩
        have hsourceU : U ⊆ e.source := fun x hx => (hOsub x hx.1).1
        have hstableU : Set.MapsTo f U U := by
          intro x hx
          exact ⟨hx.2,by change f (f x) ∈ O; rw [hinv x]; exact hx.1⟩
        have hnegU : ∀ x ∈ U, e (f x) = -e x := fun x hx => (hOsub x hx.1).2.2.2
        refine ⟨e,U,hU,hqU,hsourceU,hzero,hstableU,?_,?_,hnegU,?_⟩
        · exact fun x hx => (hOsub x hx.1).2.1
        · rintro w ⟨x,hx,rfl⟩
          exact (hOsub x hx.1).2.2.1
        · exact actual_branch_coordinate_square_fiber f e U hsourceU hstableU hnegU
      obtain ⟨e,U,hU,hq,hsource,hzero,hstable,hhol,hinvhol,hneg,hsquare⟩ := hnormal
      have hdesc :
        ∃ c : OpenPartialHomeomorph B ℂ,
          c.source = p '' U ∧ p q ∈ c.source ∧
          c.target = (fun z : ℂ => z ^ 2) '' (e '' U) ∧
          (∀ x ∈ U, c (p x) = (e x) ^ 2) := by
        let P := p '' U
        let V := e '' U
        have hP : IsOpen P := hp.isOpenMap U hU
        have hV : IsOpen V := e.isOpen_image_of_subset_source hU hsource
        let e0 : U ≃ₜ V := e.homeomorphOfImageSubsetSource hsource rfl
        let p0 : U → P := fun x => ⟨p x, ⟨x,x.property,rfl⟩⟩
        letI : Nonempty U := ⟨⟨q,hq⟩⟩
        have hp0 : IsOpenQuotientMap p0 := by
          refine ⟨?_,hp.continuous.subtype_map (q := fun y => y ∈ P) (fun x hx => ⟨x,hx,rfl⟩),
            hp.isOpenMap.subtype_map (t := P) hU (fun x hx => ⟨x,hx,rfl⟩)⟩
          intro y
          obtain ⟨x,hx,hpx⟩ := y.property
          exact ⟨⟨x,hx⟩,Subtype.ext hpx⟩
        have hker : ∀ x y : U, p0 x = p0 y ↔
            (e0 x : ℂ) = (e0 y : ℂ) ∨ (e0 x : ℂ) = -(e0 y : ℂ) := by
          intro x y
          rw [Subtype.ext_iff]
          change p x = p y ↔ e x = e y ∨ e x = -e y
          rw [hfiber y x]
          exact ((actual_branch_coordinate_square_fiber f e U hsource hstable hneg)
            y y.property x x.property).symm.trans sq_eq_sq_iff_eq_or_eq_neg
        obtain ⟨c0,hcsource,hctarget,hcformula⟩ :=
          actual_local_negation_quotient_literal_square_chart V hV e0 p0 hp0 hker
        let c := c0.lift_openEmbedding hP.isOpenEmbedding_subtypeVal
        have hcs : c.source = P := by
          rw [c0.lift_openEmbedding_source, hcsource]
          simp
        refine ⟨c,hcs,?_,hctarget,?_⟩
        · rw [hcs]
          exact ⟨q,hq,rfl⟩
        · intro x hx
          change c (Subtype.val (p0 ⟨x,hx⟩)) = (e x) ^ 2
          rw [c0.lift_openEmbedding_apply]
          exact hcformula ⟨x,hx⟩
      obtain ⟨c,hcs,hcq,hct,hcf⟩ := hdesc
      exact ⟨e,U,c,hU,hq,hsource,hzero,hstable,hhol,hinvhol,hcs,hcq,hct,hcf⟩
    have actual_J_fixed_set_finite : {x : E | J x = x}.Finite := by
      obtain ⟨F,hF,hcard⟩ := hfix
      rw [← hF]
      exact F.finite_toSet
    have actual_deck_fixed_set_finite : {x : E | M.cover.deck x = x}.Finite := by
      obtain ⟨F,hF,hcard⟩ := actual_deck_full_fixed_set
      rw [← hF]
      exact F.finite_toSet
    have actual_J_fixed_branch_square_charts {B : Type} [TopologicalSpace B]
        (p : E → B) (hp : IsOpenQuotientMap p)
        (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = J x)
        (q : E) (hfixq : J q = q) :
    ∃ (e : OpenPartialHomeomorph E ℂ) (U : Set E)
          (c : OpenPartialHomeomorph B ℂ),
          IsOpen U ∧ q ∈ U ∧ U ⊆ e.source ∧ e q = 0 ∧
          Set.MapsTo J U U ∧
          (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x) ∧
          (∀ w ∈ e '' U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w) ∧
          c.source = p '' U ∧ p q ∈ c.source ∧
          c.target = (fun z : ℂ => z ^ 2) '' (e '' U) ∧
          (∀ x ∈ U, c (p x) = (e x) ^ 2) := by
      exact actual_fixed_quotient_square_chart J hJinv actual_J_fixed_set_finite J_actual_holomorphic p hp hfiber q hfixq
    have actual_deck_fixed_branch_square_charts {B : Type} [TopologicalSpace B]
        (p : E → B) (hp : IsOpenQuotientMap p)
        (hfiber : ∀ x y, p y = p x ↔ y = x ∨ y = M.cover.deck x)
        (q : E) (hfixq : M.cover.deck q = q) :
    ∃ (e : OpenPartialHomeomorph E ℂ) (U : Set E)
          (c : OpenPartialHomeomorph B ℂ),
          IsOpen U ∧ q ∈ U ∧ U ⊆ e.source ∧ e q = 0 ∧
          Set.MapsTo M.cover.deck U U ∧
          (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x) ∧
          (∀ w ∈ e '' U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w) ∧
          c.source = p '' U ∧ p q ∈ c.source ∧
          c.target = (fun z : ℂ => z ^ 2) '' (e '' U) ∧
          (∀ x ∈ U, c (p x) = (e x) ^ 2) := by
      exact actual_fixed_quotient_square_chart M.cover.deck actual_deck_involutive actual_deck_fixed_set_finite deck_actual_holomorphic p hp hfiber q hfixq
    have actual_J_compatible_branched_double_cover :
        ∃ (B : Type) (t : TopologicalSpace B),
          letI : TopologicalSpace B := t
          T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
          ∃ Q : BranchedDoubleCover E B, Q.deck = J ∧
          ∀ x (hx : Q.projection x ∈ Q.branch),
            ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (Q.branch_chart x hx).upstairs
              (Q.branch_chart x hx).upstairs.source ∧
            ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (Q.branch_chart x hx).upstairs.symm
              (Q.branch_chart x hx).upstairs.target := by
      obtain ⟨F, hF, hcard⟩ := hfix
      exact actual_holomorphic_six_fixed_involution_compatible_branched_double_cover
        J hJinv J_actual_holomorphic F hF hcard
    have actual_deck_compatible_branched_double_cover :
        ∃ (B : Type) (t : TopologicalSpace B),
          letI : TopologicalSpace B := t
          T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
          ∃ Q : BranchedDoubleCover E B, Q.deck = M.cover.deck ∧
          ∀ x (hx : Q.projection x ∈ Q.branch),
            ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (Q.branch_chart x hx).upstairs
              (Q.branch_chart x hx).upstairs.source ∧
            ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (Q.branch_chart x hx).upstairs.symm
              (Q.branch_chart x hx).upstairs.target := by
      obtain ⟨F, hF, hcard⟩ := actual_deck_full_fixed_set
      exact actual_holomorphic_six_fixed_involution_compatible_branched_double_cover
        M.cover.deck actual_deck_involutive deck_actual_holomorphic F hF hcard
    obtain ⟨BJ, tJ, pJ, hTJ, hCompactJ, hConnectedJ,
      hpJ, hfiberJ, hregularJ, DJ, hDcardJ, hDimageJ, hDfixJ,
      hDsingletonJ, hDtwoJ⟩ := actual_J_six_branch_quotient
    letI : TopologicalSpace BJ := tJ
    letI : T2Space BJ := hTJ
    letI : CompactSpace BJ := hCompactJ
    letI : ConnectedSpace BJ := hConnectedJ
    obtain ⟨chartsJ, AJ, hChartAtJ, hAtlasJ, hManifoldJ,
      hProjectionHolomorphicJ, hLocalPowerJ⟩ :=
      actual_holomorphic_involution_quotient_literal_holomorphic_atlas
        J hJinv actual_J_fixed_set_finite J_actual_holomorphic pJ hpJ hfiberJ
    letI : ChartedSpace ℂ BJ := AJ
    letI : IsManifold 𝓘(ℂ) ∞ BJ := hManifoldJ
    obtain ⟨BDeck, tDeck, pDeck, hTDeck, hCompactDeck, hConnectedDeck,
      hpDeck, hfiberDeck, hregularDeck, DDeck, hDcardDeck, hDimageDeck, hDfixDeck,
      hDsingletonDeck, hDtwoDeck⟩ := actual_deck_six_branch_quotient
    letI : TopologicalSpace BDeck := tDeck
    letI : T2Space BDeck := hTDeck
    letI : CompactSpace BDeck := hCompactDeck
    letI : ConnectedSpace BDeck := hConnectedDeck
    obtain ⟨chartsDeck, ADeck, hChartAtDeck, hAtlasDeck, hManifoldDeck,
      hProjectionHolomorphicDeck, hLocalPowerDeck⟩ :=
      actual_holomorphic_involution_quotient_literal_holomorphic_atlas
        M.cover.deck actual_deck_involutive actual_deck_fixed_set_finite deck_actual_holomorphic pDeck hpDeck hfiberDeck
    letI : ChartedSpace ℂ BDeck := ADeck
    letI : IsManifold 𝓘(ℂ) ∞ BDeck := hManifoldDeck
    haveI : PerfectSpace E := by
      obtain ⟨F,_,hcard⟩ := hfix
      have hcard' : 1 < F.card := by omega
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hcard'
      letI : Nontrivial E := ⟨⟨a,b,hab⟩⟩
      infer_instance
    obtain ⟨F,hF,hFcard⟩ := hfix
    obtain ⟨G,hG,hGcard⟩ := actual_deck_full_fixed_set
    have actual_canonical_global_data :
        ∃ b : Module.Basis (Fin 2) ℂ (ActualCanonicalSection E),
          (∀ x : E, actualCanonicalEvaluation x ≠ 0) ∧
          (∀ s : ActualCanonicalSection E, s ≠ 0 →
            ∃ Z : Finset E, Z.card ≤ 2 ∧ ∀ x : E, s x = 0 → x ∈ Z) := by
      obtain ⟨b⟩ := actual_genus_two_holomorphic_cotangent_dimension_two
        E M.genusTwo actualComplexAtlas actualComplexManifold
      have hbase : ∀ x : E, actualCanonicalEvaluation x ≠ 0 :=
        (CanonicalDimensionTwo.actualPointDetection_iff_evaluation_nonzero
          E M.genusTwo actualComplexAtlas actualComplexManifold).mp
            (CanonicalDimensionTwo.actualPointMittagLefflerDetection
              E M.genusTwo actualComplexAtlas actualComplexManifold)
      refine ⟨b, hbase, ?_⟩
      intro s hs
      obtain ⟨Z, hZ, hsum⟩ := actual_genus_two_canonical_section_zero_order_sum
        E M.genusTwo actualComplexAtlas actualComplexManifold s hs
      have hpos : ∀ x ∈ Z, 0 < actualCanonicalZeroOrder s x := by
        intro x hx
        apply (actual_canonical_section_finite_positive_zero_orders s hs x).2
        have hm : x ∈ (Z : Set E) := hx
        rw [hZ] at hm
        exact hm
      refine ⟨Z, ?_, ?_⟩
      · calc
          Z.card = ∑ x ∈ Z, (1 : ℕ) := by simp
          _ ≤ ∑ x ∈ Z, actualCanonicalZeroOrder s x :=
            Finset.sum_le_sum (fun x hx => hpos x hx)
          _ = 2 := hsum
      · intro x hx
        have hm : x ∈ (Z : Set E) := by rw [hZ]; exact hx
        exact hm
    obtain ⟨b,hbase,hzeros⟩ := actual_canonical_global_data
    exact actual_canonical_section_two_involutions_uniqueness_reduction
      b hbase hzeros J M.cover.deck J_actual_holomorphic deck_actual_holomorphic
      hJinv actual_deck_involutive F G hF hFcard hG hGcard
  )

end CurveComplex.Hyperbolic
