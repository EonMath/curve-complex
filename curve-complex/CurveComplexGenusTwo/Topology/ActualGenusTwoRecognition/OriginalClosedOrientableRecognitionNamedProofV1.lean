import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereProbe
import Mathlib.Analysis.Normed.Module.Connected
import CurveComplexGenusTwo.Dictionary.Genus
import ClassificationOfSurfaces.EvalStatement
import CurveComplexGenusTwo.Topology.ActualCrosscapGeometry.RawCrosscapSquareStrip
import CurveComplexGenusTwo.Topology.ActualCutRecognition.TwistedBandReflectionExportStatement
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ActualOrientableBoundaryOfAtlas
open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Manifold ContDiff
open CurveComplex CurveComplexGenusTwo.CWHurewicz
open LeanEval.Topology.ClassificationOfSurfaces
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
theorem actual_original_genus_two_closed_orientable_recognition (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2) :
    ∃ p : ℕ, 1 ≤ p ∧ Nonempty (S ≃ₜ Quot (OrientableRel p 0)) := by
  have hmodels : ∃ p n, ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
      (1 ≤ p ∧ Nonempty (S ≃ₜ Quot (NonOrientableRel p n))) := by
    have hgeneric : Nonempty (S ≃ₜ SphereRepresentative) ∨
        ∃ p n, ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧ Nonempty (S ≃ₜ Quot (NonOrientableRel p n))) := by
      classical
      letI : ClosedSurface S := Classical.choice hS.2.1
      have hpositiveAmbientCharts :
          ∃ charts : ChartedSpace (EuclideanHalfSpace 2) S,
            letI := charts
            ∀ x : S, 0 < ((chartAt (EuclideanHalfSpace 2) x) x).val 0 := by
        let P := EuclideanSpace ℝ (Fin 2)
        let h : P ≃ₜ ℝ × ℝ :=
          (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow (X := ℝ))
        let e : OpenPartialHomeomorph P P := h.toOpenPartialHomeomorph.trans
          ((Real.expPartialHomeomorph.prod (OpenPartialHomeomorph.refl ℝ)).trans
            h.symm.toOpenPartialHomeomorph)
        have es : e.source = univ := by simp [e]
        have et : e.target = {x : P | 0 < x 0} := by
          ext x
          simp [e, h, Homeomorph.finTwoArrow, Real.expPartialHomeomorph]
          rfl
        have ep (x : P) : 0 < e x 0 := by
          have hh := e.map_source (show x ∈ e.source by rw [es]; trivial)
          rwa [et] at hh
        let a : OpenPartialHomeomorph P (EuclideanHalfSpace 2) := {
          toFun := fun x => ⟨e x, le_of_lt (ep x)⟩
          invFun := fun y => e.symm y.val
          source := univ
          target := {y | 0 < y.val 0}
          map_source' := fun x _ => ep x
          map_target' := fun _ _ => mem_univ _
          left_inv' := fun x _ => e.left_inv (by rw [es]; trivial)
          right_inv' := by
            intro y hy
            apply Subtype.ext
            exact e.right_inv (by rwa [et])
          open_source := isOpen_univ
          open_target := isOpen_lt continuous_const
            (((continuous_apply 0).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous).comp continuous_subtype_val)
          continuousOn_toFun := by
            apply Continuous.continuousOn
            exact (continuousOn_univ.mp (by simpa only [es] using e.continuousOn)).subtype_mk _
          continuousOn_invFun := by
            apply e.symm.continuousOn.comp continuous_subtype_val.continuousOn
            intro y hy
            rwa [e.symm_source, et]
        }
        letI : ChartedSpace (EuclideanHalfSpace 2) P := {
          atlas := {a}
          chartAt := fun _ => a
          mem_chart_source := fun _ => mem_univ _
          chart_mem_atlas := fun _ => mem_singleton _
        }
        refine ⟨ChartedSpace.comp (EuclideanHalfSpace 2) P S, ?_⟩
        intro x
        change 0 < (a ((chartAt P x) x)).val 0
        exact ep ((chartAt P x) x)
      obtain ⟨charts, hpositive⟩ := hpositiveAmbientCharts
      letI : ChartedSpace (EuclideanHalfSpace 2) S := charts
      letI : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S := by infer_instance
      exact classification_of_surfaces S
    have hnoSphere : ¬ Nonempty (S ≃ₜ SphereRepresentative) := by
      have hSphereZero : IsZero (CurveComplex.integralHomology SphereRepresentative 1) := by
        classical
        let puncturedChart (n : ℕ) (v : SphereSpace n) :
            ↥({v}ᶜ : Set (SphereSpace n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
          exact (Homeomorph.setCongr (stereographic'_source v).symm).trans
            ((stereographic' n v).toHomeomorphSourceTarget.trans
              ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))
        
        have puncturedChart_antipode (n : ℕ) (v : SphereSpace n) :
            puncturedChart n v ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm⟩ = 0 := by
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) := ⟨by simp⟩
          change (stereographic' n v) (-v) = 0
          simp [stereographic', stereographic_apply_neg]
        
        have punctured_contractible (n : ℕ) (v : SphereSpace n) :
            ContractibleSpace ↥({v}ᶜ : Set (SphereSpace n)) :=
          (puncturedChart n v).contractibleSpace
        
        let overlapChart (n : ℕ) (v : SphereSpace n) :
            ↥(({v}ᶜ : Set (SphereSpace n)) ∩ {-v}ᶜ) ≃ₜ
              ↥({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := {
          toFun x := ⟨puncturedChart n v ⟨x.val, x.property.1⟩, by
            change puncturedChart n v ⟨x.val, x.property.1⟩ ≠ 0
            rw [← puncturedChart_antipode n v]
            intro h
            have hh := congrArg Subtype.val ((puncturedChart n v).injective h)
            exact x.property.2 hh⟩
          invFun y := ⟨((puncturedChart n v).symm y.val).val,
            ((puncturedChart n v).symm y.val).property, by
            change ((puncturedChart n v).symm y.val).val ≠ -v
            intro h
            apply y.property
            have hh : (puncturedChart n v).symm y.val =
                ⟨-v, by simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm⟩ := Subtype.ext h
            have := congrArg (puncturedChart n v) hh
            simpa [puncturedChart_antipode] using this⟩
          left_inv x := by apply Subtype.ext; simp
          right_inv y := by apply Subtype.ext; simp
          continuous_toFun := by
            apply Continuous.subtype_mk
            exact (puncturedChart n v).continuous.comp (continuous_subtype_val.subtype_mk _)
          continuous_invFun := by
            apply Continuous.subtype_mk
            exact continuous_subtype_val.comp ((puncturedChart n v).symm.continuous.comp continuous_subtype_val)
        
        }
        
        have antipodal_open_cover (n : ℕ) (v : SphereSpace n) :
            ({v}ᶜ : Set (SphereSpace n)) ∪ {-v}ᶜ = univ := by
          ext x
          simp only [mem_union, mem_compl_iff, mem_singleton_iff, mem_univ, iff_true]
          by_cases h : x = v
          · right
            subst x
            exact ne_neg_of_mem_unit_sphere ℝ v
          · exact Or.inl h
        
        let v : SphereSpace 2 := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by
          rw [Metric.mem_sphere,dist_zero_right]
          exact (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 0⟩
        let X := TopCat.of (SphereSpace 2)
        let U : Set X := {v}ᶜ
        let V : Set X := {-v}ᶜ
        let hU : IsOpen U := isClosed_singleton.isOpen_compl
        let hV : IsOpen V := isClosed_singleton.isOpen_compl
        let hc : U ∪ V = univ := antipodal_open_cover 2 v
        letI : ContractibleSpace U := punctured_contractible 2 v
        letI : ContractibleSpace V := punctured_contractible 2 (-v)
        letI : PathConnectedSpace ↥({(0 : EuclideanSpace ℝ (Fin 2))}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
          isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_singleton_of_one_lt_rank (Module.one_lt_rank_of_one_lt_finrank (by simp)) (0 : EuclideanSpace ℝ (Fin 2)))
        letI : PathConnectedSpace ↥(U ∩ V) := (overlapChart 2 v).symm.pathConnectedSpace
        let RZ := ModuleCat.of ℤ ℤ
        let F := (singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj RZ
        let inc : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
          TopCat.ofHom ⟨fun x => ⟨x.val,x.property.1⟩,by fun_prop⟩
        have hg : Function.Injective (actualMVDifference X U V 0) := by
          apply (injective_iff_map_eq_zero (actualMVDifference X U V 0).hom).mpr
          intro x hx
          have hxu := congrArg Prod.fst hx
          rw [actualMVDifference_apply] at hxu
          change F.map inc x = 0 at hxu
          have he := CircleHomologyComputation.augmentation_naturality inc
          have hex := congrArg (fun m => m x) he
          change (TopCat.of U).singularHomology₀ε RZ (F.map inc x) =
            (TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ x at hex
          rw [hxu,map_zero] at hex
          have hi := (ModuleCat.mono_iff_injective ((TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ)).mp
            (inferInstance : Mono ((TopCat.of ↥(U ∩ V)).singularHomology₀ε RZ))
          apply hi
          simpa using hex.symm
        have hu1 : IsZero (H U 1) := CircleHomologyComputation.contractible_positive_homology U 1 (by omega)
        have hv1 : IsZero (H V 1) := CircleHomologyComputation.contractible_positive_homology V 1 (by omega)
        letI := ModuleCat.subsingleton_of_isZero hu1
        letI := ModuleCat.subsingleton_of_isZero hv1
        have hz (x : H X 1) : x = 0 := by
          have hd : actualMVConnecting X U V hU hV hc 0 x = 0 := by
            apply hg
            have he := congrArg (fun m => m x) (actualMVConnecting_difference X U V hU hV hc 0)
            simpa using he
          obtain ⟨y,hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
            (actualMV_exact_ambient X U V hU hV hc 0) x hd
          have hy0 : y=0 := Subsingleton.elim _ _
          simpa [hy0] using hy.symm
        apply ModuleCat.isZero_iff_subsingleton.mpr
        exact ⟨fun x y => (hz x).trans (hz y).symm⟩
      rintro ⟨e⟩
      obtain ⟨H⟩ := hS.2.2.2
      have he := CircleHomologyComputation.homotopyHomologyIso e.toHomotopyEquiv 1
      have hzero : IsZero (CurveComplex.integralHomology S 1) := hSphereZero.of_iso he
      have hzero4 : IsZero (ModuleCat.of ℤ (Fin 4 → ℤ)) := hzero.of_iso H.symm
      letI := ModuleCat.subsingleton_of_isZero hzero4
      have h : (fun _ : Fin 4 => (1 : ℤ)) = (fun _ : Fin 4 => (0 : ℤ)) := Subsingleton.elim _ _
      have hh := congrFun h 0
      norm_num at hh
    exact hgeneric.resolve_left hnoSphere
  have hnon (p n : ℕ) (hp : 1 ≤ p) : ¬ Nonempty (S ≃ₜ Quot (NonOrientableRel p n)) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    rintro ⟨e⟩
    obtain ⟨ε,hε,square,band,hs,hb,hbottom,htop,hmeet⟩ :=
      Hyperbolic.actual_nonorientable_normal_form_first_crosscap_square_strip p n hp
    let squareS := e.symm ∘ square
    let bandS := e.symm ∘ band
    have hsS : IsEmbedding squareS := e.symm.isEmbedding.comp hs
    have hbS : IsEmbedding bandS := e.symm.isEmbedding.comp hb
    have hbottomS : ∀ t, bandS (0,t) = squareS (squarePort ε hε 2 t) := by
      intro t
      exact congrArg e.symm (hbottom t)
    have htopS : ∀ t, bandS (1,t) = squareS (squarePort ε hε 0 (flipBandWidth true t)) := by
      intro t
      exact congrArg e.symm (htop t)
    have hmeetS : Set.range bandS ∩ Set.range squareS =
        Set.range (fun t => squareS (squarePort ε hε 2 t)) ∪
        Set.range (fun t => squareS (squarePort ε hε 0 t)) := by
      change Set.range (e.symm ∘ band) ∩ Set.range (e.symm ∘ square) =
        Set.range (e.symm ∘ (fun t => square (squarePort ε hε 2 t))) ∪
        Set.range (e.symm ∘ (fun t => square (squarePort ε hε 0 t)))
      simp only [Set.range_comp]
      rw [←Set.image_inter e.symm.injective,hmeet,Set.image_union]
    obtain ⟨x,⟨W⟩⟩ := LocalSurgery.actual_square_twisted_band_produces_local_reflection
      S ε hε squareS hsS bandS hbS hbottomS htopS hmeetS
    exact GenusOrientationCandidate.no_local_reflection_witness 2 hS x
      (GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) W
  have hbZero (p n : ℕ) (hadmissible : 1 ≤ p ∨ 1 ≤ n)
      (e : S ≃ₜ Quot (OrientableRel p n)) : n = 0 := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    have hpositiveAmbientCharts :
        ∃ charts : ChartedSpace (EuclideanHalfSpace 2) S,
          letI := charts
          ∀ x : S, 0 < ((chartAt (EuclideanHalfSpace 2) x) x).val 0 := by
      let P := EuclideanSpace ℝ (Fin 2)
      let h : P ≃ₜ ℝ × ℝ :=
        (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow (X := ℝ))
      let e : OpenPartialHomeomorph P P := h.toOpenPartialHomeomorph.trans
        ((Real.expPartialHomeomorph.prod (OpenPartialHomeomorph.refl ℝ)).trans
          h.symm.toOpenPartialHomeomorph)
      have es : e.source = univ := by simp [e]
      have et : e.target = {x : P | 0 < x 0} := by
        ext x
        simp [e, h, Homeomorph.finTwoArrow, Real.expPartialHomeomorph]
        rfl
      have ep (x : P) : 0 < e x 0 := by
        have hh := e.map_source (show x ∈ e.source by rw [es]; trivial)
        rwa [et] at hh
      let a : OpenPartialHomeomorph P (EuclideanHalfSpace 2) := {
        toFun := fun x => ⟨e x, le_of_lt (ep x)⟩
        invFun := fun y => e.symm y.val
        source := univ
        target := {y | 0 < y.val 0}
        map_source' := fun x _ => ep x
        map_target' := fun _ _ => mem_univ _
        left_inv' := fun x _ => e.left_inv (by rw [es]; trivial)
        right_inv' := by
          intro y hy
          apply Subtype.ext
          exact e.right_inv (by rwa [et])
        open_source := isOpen_univ
        open_target := isOpen_lt continuous_const
          (((continuous_apply 0).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous).comp continuous_subtype_val)
        continuousOn_toFun := by
          apply Continuous.continuousOn
          exact (continuousOn_univ.mp (by simpa only [es] using e.continuousOn)).subtype_mk _
        continuousOn_invFun := by
          apply e.symm.continuousOn.comp continuous_subtype_val.continuousOn
          intro y hy
          rwa [e.symm_source, et]
      }
      letI : ChartedSpace (EuclideanHalfSpace 2) P := {
        atlas := {a}
        chartAt := fun _ => a
        mem_chart_source := fun _ => mem_univ _
        chart_mem_atlas := fun _ => mem_singleton _
      }
      refine ⟨ChartedSpace.comp (EuclideanHalfSpace 2) P S, ?_⟩
      intro x
      change 0 < (a ((chartAt P x) x)).val 0
      exact ep ((chartAt P x) x)
    obtain ⟨charts,hpositive⟩ := hpositiveAmbientCharts
    letI : ChartedSpace (EuclideanHalfSpace 2) S := charts
    let modelCharts : ChartedSpace (EuclideanHalfSpace 2) (Quot (OrientableRel p n)) := {
      atlas := Set.range (fun y => e.symm.toOpenPartialHomeomorph.trans
        (chartAt (EuclideanHalfSpace 2) (e.symm y)))
      chartAt := fun y => e.symm.toOpenPartialHomeomorph.trans
        (chartAt (EuclideanHalfSpace 2) (e.symm y))
      mem_chart_source := fun y => ⟨Set.mem_univ y,mem_chart_source _ _⟩
      chart_mem_atlas := fun y => Set.mem_range_self y
    }
    letI := modelCharts
    letI : TopologicalSpace (Fin n) := ⊥
    obtain ⟨⟨hb⟩,hsecond⟩ := Hyperbolic.actual_orientable_normal_form_intrinsic_boundary_components_of_atlas p n hadmissible modelCharts
    have hInterior (y : Quot (OrientableRel p n)) :
        (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint y := by
      apply (InvarianceOfDomain.isInteriorPoint_iff_any_chart
        (modelWithCornersEuclideanHalfSpace 2) (mem_chart_source (EuclideanHalfSpace 2) y)).mpr
      rw [interior_range_modelWithCornersEuclideanHalfSpace]
      change 0 < ((chartAt (EuclideanHalfSpace 2) y) y).val 0
      change 0 < ((chartAt (EuclideanHalfSpace 2) (e.symm y)) (e.symm y)).val 0
      exact hpositive (e.symm y)
    by_contra hn0
    have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let b := hb.symm ((⟨0,hn⟩ : Fin n),(1 : Circle))
    exact ((modelWithCornersEuclideanHalfSpace 2).isInteriorPoint_iff_not_isBoundaryPoint b.val).mp
      (hInterior b.val) b.property
  obtain ⟨p,n,hm⟩ := hmodels
  rcases hm with ⟨hadmissible,⟨e⟩⟩ | ⟨hp,he⟩
  · have hn := hbZero p n hadmissible e
    subst n
    exact ⟨p,by omega,⟨e⟩⟩
  · exact (hnon p n hp he).elim
