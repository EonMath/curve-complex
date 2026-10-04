import actual_genus_two_local_orientation_classPROVED
import CurveComplexGenusTwo.Topology.Orientation.SurfaceLocalization
import CurveComplexGenusTwo.Topology.LocalOrientation.LocalReflectionGerm
open Set Topology unitInterval Schoenflies
open scoped NNReal
open CategoryTheory CategoryTheory.Limits
open CurveComplex CurveComplexGenusTwo.CWHurewicz
open CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace CurveComplex.Hyperbolic
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_genus_two_complex_chart_orientation_sections (M : HyperellipticModel E S) :
    ∃ z : H E 2, z ≠ 0 ∧
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
  have plane_sections (M : HyperellipticModel E S) :
      ∃ z : H E 2, z ≠ 0 ∧
        (∀ x : E, homologyToRelative E ({x}ᶜ : Set E) 2 z ≠ 0) ∧
        ∃ φ : relativeHomology Plane ({0}ᶜ : Set Plane) 2 ≅ ModuleCat.of ℤ ℤ,
          ∀ e : OpenPartialHomeomorph E Plane,
            let W := e.source
            let A (x : W) : Set W := {y | y.val ≠ x.val}
            let P : Set Plane := {0}ᶜ
            let k (x : W) : C(W,Plane) := ⟨fun y => e y.val - e x.val,
              (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
            ∃ n : W → ℤ, IsLocallyConstant n ∧ ∀ x : W,
              n x ≠ 0 ∧ ∃ v : relativeHomology W (A x) 2,
                ∃ hpres : ∀ y ∈ A x, k x y ∈ P,
                  pairRelativeHomologyMap (A x) ({x.val}ᶜ : Set E) (ReflectionGermProof.inclusion W)
                    (fun y hy => hy) 2 v = homologyToRelative E ({x.val}ᶜ : Set E) 2 z ∧
                  n x = φ.hom (pairRelativeHomologyMap (A x) P (k x) hpres 2 v) := by
    have plane_local_integer_iso : Nonempty (relativeHomology Schoenflies.Plane ({0}ᶜ : Set Schoenflies.Plane) 2 ≅
        ModuleCat.of ℤ ℤ) := by
      have product_plane_iso : Nonempty (relativeHomology (ℝ × ℝ) ({(0,0)}ᶜ : Set (ℝ × ℝ)) 2 ≅
          ModuleCat.of ℤ ℤ) := by
        let P : Set (ℝ × ℝ) := {(0,0)}ᶜ
        have hz2 : IsZero (H (ℝ × ℝ) 2) :=
          CircleHomologyComputation.contractible_positive_homology (ℝ × ℝ) 2 (by decide)
        have hz1 : IsZero (H (ℝ × ℝ) 1) :=
          CircleHomologyComputation.contractible_positive_homology (ℝ × ℝ) 1 (by decide)
        obtain ⟨_,he2⟩ := pairHomology_exact_at_relative (ℝ × ℝ) P 1
        obtain ⟨_,he1⟩ := pairHomology_exact_at_subspace (ℝ × ℝ) P 1
        haveI : Mono (relativeConnecting (ℝ × ℝ) P 1) := he2.mono_g (hz2.eq_of_src _ _)
        haveI : Epi (relativeConnecting (ℝ × ℝ) P 1) := he1.epi_f (hz1.eq_of_tgt _ _)
        haveI : IsIso (relativeConnecting (ℝ × ℝ) P 1) := isIso_of_mono_of_epi _
        exact ⟨asIso (relativeConnecting (ℝ × ℝ) P 1) ≪≫ circlePlaneH1Iso.symm ≪≫
          CircleHomologyComputation.circleH1Iso⟩
      let e : Schoenflies.Plane ≃ₜ ℝ × ℝ :=
        (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans Homeomorph.finTwoArrow
      have h0 : e 0 = (0,0) := by apply Prod.ext <;> rfl
      have hf : ∀ x ∈ ({0}ᶜ : Set Schoenflies.Plane), e x ∈ ({(0,0)}ᶜ : Set (ℝ × ℝ)) := by
        intro x hx hh
        exact hx (e.injective (hh.trans h0.symm))
      have hi : ∀ y ∈ ({(0,0)}ᶜ : Set (ℝ × ℝ)), e.symm y ∈ ({0}ᶜ : Set Schoenflies.Plane) := by
        intro y hy hh
        exact hy ((congrArg e hh).trans h0)
      haveI : IsIso (pairRelativeHomologyMap ({0}ᶜ : Set Schoenflies.Plane)
          ({(0,0)}ᶜ : Set (ℝ × ℝ)) ⟨e,e.continuous⟩ hf 2) :=
        ReflectionGermProof.pairHomeo_isIso _ _ e hf hi 2
      obtain ⟨φ⟩ := product_plane_iso
      exact ⟨asIso (pairRelativeHomologyMap ({0}ᶜ : Set Schoenflies.Plane)
        ({(0,0)}ᶜ : Set (ℝ × ℝ)) ⟨e,e.continuous⟩ hf 2) ≪≫ φ⟩
    have chart_integer_section (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
        (E : OpenPartialHomeomorph S Plane)
        (φ : relativeHomology Plane ({0}ᶜ : Set Plane) 2 ≅ ModuleCat.of ℤ ℤ) (z : H S 2) :
        let W := E.source
        let A (x : W) : Set W := {y | y.val ≠ x.val}
        let P : Set Plane := {0}ᶜ
        let k (x : W) : C(W,Plane) := ⟨fun y => E y.val - E x.val,
          (E.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
        ∃ n : W → ℤ, IsLocallyConstant n ∧ ∀ x : W,
          ∃ v : relativeHomology W (A x) 2, ∃ hpres : ∀ y ∈ A x, k x y ∈ P,
            pairRelativeHomologyMap (A x) ({x.val}ᶜ : Set S) (ReflectionGermProof.inclusion W)
              (fun y hy => hy) 2 v = homologyToRelative S ({x.val}ᶜ : Set S) 2 z ∧
            n x = φ.hom (pairRelativeHomologyMap (A x) P (k x) hpres 2 v) ∧
            (n x = 0 ↔ homologyToRelative S ({x.val}ᶜ : Set S) 2 z = 0) := by
      have moving_chart_classes (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
          (p : S) (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) :
          let W := E.source
          let A (x : S) : Set W := {y | y.val ≠ x}
          let P : Set Plane := {0}ᶜ
          let k (x : S) : C(W,Plane) := ⟨fun y => E y.val - E x,
            (E.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
          ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ E.source ∧
            ∀ q ∈ U, ∀ z : H S 2,
              ∃ vp : relativeHomology W (A p) 2, ∃ vq : relativeHomology W (A q) 2,
                pairRelativeHomologyMap (A p) ({p}ᶜ : Set S) (ReflectionGermProof.inclusion W)
                  (fun y hy => hy) 2 vp = homologyToRelative S ({p}ᶜ : Set S) 2 z ∧
                pairRelativeHomologyMap (A q) ({q}ᶜ : Set S) (ReflectionGermProof.inclusion W)
                  (fun y hy => hy) 2 vq = homologyToRelative S ({q}ᶜ : Set S) 2 z ∧
                ∃ hkp : ∀ y ∈ A p, k p y ∈ P, ∃ hkq : ∀ y ∈ A q, k q y ∈ P,
                  pairRelativeHomologyMap (A p) P (k p) hkp 2 vp =
                    pairRelativeHomologyMap (A q) P (k q) hkq 2 vq := by
        have given_chart_point_motion (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
            (p : S) (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) :
            ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
              ∀ q ∈ U, ∃ G : AmbientIsotopy S, ∃ H : AmbientIsotopy Plane,
                G.finalMap p = q ∧ ∀ t y, y ∈ E.source →
                  G.map (t,y) ∈ E.source ∧ E (G.map (t,y)) = H.map (t,E y) := by
          classical
          have hsmall (f : Plane → Plane)
                (c : ℝ≥0) (hc : (c : ℝ) < 1) (hf : LipschitzWith c f) :
                ∃ H : AmbientIsotopy Plane,
                  (∀ t x, H.map (t, x) = x + (t : ℝ) • f x) ∧
                  (∀ t x, f x = 0 → H.map (t, x) = x) := by
            classical
            let F : Interval × Plane → Plane :=
              fun p => p.2 + (p.1 : ℝ) • f p.2
            have hF : Continuous F := continuous_snd.add
              ((continuous_subtype_val.comp continuous_fst).smul
                (hf.continuous.comp continuous_snd))
            refine ⟨{ map := ⟨F, hF⟩, homeomorphism_at := ?_, at_zero := ?_ },
              fun t x => rfl, ?_⟩
            · intro t
              have happ : ApproximatesLinearOn (fun x => F (t, x))
                  (ContinuousLinearEquiv.refl ℝ Plane : Plane →L[ℝ] Plane)
                  Set.univ c := by
                intro x _ y _
                have heq : F (t, x) - F (t, y) - (x - y) =
                    (t : ℝ) • (f x - f y) := by dsimp [F]; module
                change ‖F (t, x) - F (t, y) - (x - y)‖ ≤ _
                rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
                calc
                  (t : ℝ) * ‖f x - f y‖ ≤ 1 * ‖f x - f y‖ :=
                    mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
                  _ ≤ c * ‖x - y‖ := by simpa [dist_eq_norm] using hf.dist_le_mul x y
              let e := happ.toHomeomorph (fun x => F (t, x)) (Or.inr (by simpa using hc))
              exact ⟨e, fun x => rfl⟩
            · intro x
              simp [F]
            · intro t x hx
              change x + (t : ℝ) • f x = x
              simp [hx]
          
          have hpush (p v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < 1) :
                ∃ H : AmbientIsotopy Plane,
                  (∀ x, H.finalMap x = x + max (R - dist x p) 0 • v) ∧
                  ∀ t x, R ≤ dist x p → H.map (t, x) = x := by
            classical
            let b : Plane → ℝ := fun x => max (R - dist x p) 0
            have hb0 : LipschitzWith 1 (fun x : Plane => R - dist x p) := by
              apply LipschitzWith.of_dist_le_mul
              intro x y
              simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
                sub_sub_sub_cancel_left, abs_sub_comm] using abs_dist_sub_le x y p
            have hb : LipschitzWith 1 b := hb0.max_const 0
            let f : Plane → Plane := fun x => b x • v
            have hf : LipschitzWith ‖v‖₊ f := by
              apply LipschitzWith.of_dist_le_mul
              intro x y
              change ‖b x • v - b y • v‖ ≤ ‖v‖ * dist x y
              rw [← sub_smul, norm_smul, Real.norm_eq_abs]
              have h := hb.dist_le_mul x y
              simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
              calc
                |b x - b y| * ‖v‖ ≤ dist x y * ‖v‖ :=
                  mul_le_mul_of_nonneg_right h (norm_nonneg _)
                _ = ‖v‖ * dist x y := mul_comm _ _
            obtain ⟨H, hH, hfix⟩ := hsmall f ‖v‖₊ hv hf
            refine ⟨H, ?_, ?_⟩
            · intro x
              unfold AmbientIsotopy.finalMap
              rw [hH]
              simp [f, b]
            · intro t x hx
              apply hfix
              simp [f, b, max_eq_right (sub_nonpos.mpr hx)]
          obtain ⟨r, hr, hrE⟩ := Metric.isOpen_iff.mp E.open_target
            (E p) (E.map_source hpE)
          let R : ℝ := r / 2
          have hR : 0 < R := by dsimp [R]; positivity
          have hRr : R < r := by dsimp [R]; linarith
          have hCV : Metric.closedBall (E p) R ⊆ E.target :=
            (Metric.closedBall_subset_ball hRr).trans hrE
          let U : Set S := E.source ∩ E ⁻¹' Metric.ball (E p) R
          have hU : IsOpen U :=
            E.continuousOn_toFun.isOpen_inter_preimage E.open_source Metric.isOpen_ball
          have hpU : p ∈ U := ⟨hpE, Metric.mem_ball_self hR⟩
          refine ⟨U, hU, hpU, ?_⟩
          intro q hq
          let v : Plane := R⁻¹ • (E q - E p)
          have hv : ‖v‖ < 1 := by
            have hdist : ‖E q - E p‖ < R := by
              simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hq.2
            dsimp [v]
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
            calc
              R⁻¹ * ‖E q - E p‖ = ‖E q - E p‖ / R := by rw [div_eq_mul_inv, mul_comm]
              _ < 1 := (div_lt_one hR).mpr hdist
          obtain ⟨H, hmove, hfix⟩ := hpush (E p) v R hR hv
          have hcenter : H.finalMap (E p) = E q := by
            rw [hmove]
            simp only [dist_self, sub_zero, max_eq_left hR.le]
            dsimp [v]
            rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
            module
          obtain ⟨K, G, hcoord, hGU, hGfix⟩ := position_surface_chart_lift S
            E.source E.target E.open_source E.toHomeomorphSourceTarget
            (Metric.closedBall (E p) R) (isCompact_closedBall _ _) hCV H (by
              intro t x hx
              apply hfix
              have hh : ¬ dist x (E p) ≤ R := hx
              exact (lt_of_not_ge hh).le)
          have hpoint : K.finalMap ⟨p,hpE⟩ = ⟨q,hq.1⟩ := by
            apply Subtype.ext
            apply E.injOn (K.finalMap ⟨p,hpE⟩).property hq.1
            have hh := hcoord (⟨1, by norm_num⟩ : Interval) ⟨p,hpE⟩
            change E (K.finalMap ⟨p,hpE⟩).val = H.finalMap (E p) at hh
            exact hh.trans hcenter
          refine ⟨G,H,?_,?_⟩
          · have he := hGU (⟨1, by norm_num⟩ : Interval) ⟨p,hpE⟩
            change G.finalMap p = (K.finalMap ⟨p,hpE⟩).val at he
            rw [hpoint] at he
            exact he
          · intro t y hy
            have he := hGU t ⟨y,hy⟩
            rw [he]
            exact ⟨(K.map (t,⟨y,hy⟩)).property,hcoord t ⟨y,hy⟩⟩
        have moving_center_identity {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (H : AmbientIsotopy V) (p : V)
            (f : C(V,V))
            (hf : ∀ z, f z = H.finalMap (z + p) - H.finalMap p)
            (hpres : ∀ z ∈ ({(0 : V)}ᶜ : Set V), f z ∈ ({(0 : V)}ᶜ : Set V)) :
            pairRelativeHomologyMap ({(0 : V)}ᶜ : Set V) ({(0 : V)}ᶜ : Set V)
              f hpres 2 = 𝟙 (relativeHomology V ({(0 : V)}ᶜ : Set V) 2) := by
          let P : Set V := {(0 : V)}ᶜ
          let F (t : unitInterval) (z : V) : V := H.map (t,z+p) - H.map (t,p)
          have hF (t : unitInterval) (z : V) (hz : z ∈ P) : F t z ∈ P := by
            intro heq
            apply hz
            change F t z = 0 at heq
            have hh : H.map (t,z+p) = H.map (t,p) := sub_eq_zero.mp heq
            obtain ⟨e,he⟩ := H.homeomorphism_at t
            have hzp : z + p = p := e.injective ((he _).trans (hh.trans (he _).symm))
            change z = (0 : V)
            exact add_right_cancel (show z+p = (0 : V)+p by simpa only [zero_add] using hzp)
          let fp : C(P,P) := ⟨fun z => ⟨f z.val,hpres z.val z.property⟩,
            (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
          let K : ContinuousMap.Homotopy (ContinuousMap.id P) fp := {
            toContinuousMap := ⟨fun a => ⟨F a.1 a.2.val,hF a.1 a.2.val a.2.property⟩,by
              apply Continuous.subtype_mk
              dsimp [F]
              fun_prop⟩
            map_zero_left := by
              intro z
              apply Subtype.ext
              change H.map (⟨0,by norm_num⟩,z.val+p) - H.map (⟨0,by norm_num⟩,p) = z.val
              rw [H.at_zero,H.at_zero]
              abel
            map_one_left := by
              intro z
              apply Subtype.ext
              exact (hf z.val).symm }
          let G := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
            (ModuleCat.of ℤ ℤ)
          let Ktop : TopCat.Homotopy (𝟙 (TopCat.of P)) (pairMapOnSubspace P P f hpres) := K
          have hh := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
            Ktop (ModuleCat.of ℤ ℤ) 1
          change G.map (𝟙 (TopCat.of P)) = G.map (pairMapOnSubspace P P f hpres) at hh
          rw [CategoryTheory.Functor.map_id] at hh
          have hz : IsZero (CurveComplexGenusTwo.CWHurewicz.H V 2) :=
            CircleHomologyComputation.contractible_positive_homology V 2 (by decide)
          obtain ⟨_,he⟩ := pairHomology_exact_at_relative V P 1
          haveI : Mono (relativeConnecting V P 1) := he.mono_g (hz.eq_of_src _ _)
          apply (cancel_mono (relativeConnecting V P 1)).1
          have hn := relativeConnecting_natural P P f hpres 1
          change relativeConnecting V P 1 ≫ G.map (pairMapOnSubspace P P f hpres) =
            pairRelativeHomologyMap P P f hpres 2 ≫ relativeConnecting V P 1 at hn
          rw [←hh,Category.comp_id] at hn
          simpa only [Category.id_comp] using hn.symm
        dsimp only
        let W := E.source
        let A (x : S) : Set W := {y | y.val ≠ x}
        let P : Set Plane := {0}ᶜ
        let k (x : S) : C(W,Plane) := ⟨fun y => E y.val - E x,
          (E.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
        obtain ⟨U,hU,hpU,hmove⟩ := given_chart_point_motion S p E hpE
        let V := U ∩ E.source
        refine ⟨V,hU.inter E.open_source,⟨hpU,hpE⟩,Set.inter_subset_right,?_⟩
        intro q hq z
        obtain ⟨G,H,hpq,hcoord⟩ := hmove q hq.1
        have hpqplane : H.finalMap (E p) = E q := by
          have hh := (hcoord ⟨1,by norm_num⟩ p hpE).2
          change E (G.finalMap p) = H.finalMap (E p) at hh
          rw [hpq] at hh
          exact hh.symm
        obtain ⟨e,he⟩ := G.homeomorphism_at ⟨1,by norm_num⟩
        have hepq : e p = q := (he p).trans hpq
        let f : C(S,S) := ⟨e,e.continuous⟩
        have hfp : ∀ y ∈ ({p}ᶜ : Set S), f y ∈ ({q}ᶜ : Set S) := by
          intro y hy heq
          apply hy
          change y = p
          exact e.injective (heq.trans hepq.symm)
        let g : C(W,W) := ⟨fun y => ⟨f y.val,(he y.val) ▸ (hcoord ⟨1,by norm_num⟩ y.val y.property).1⟩,
          (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
        have hgp : ∀ y ∈ A p, g y ∈ A q := by
          intro y hy heq
          exact hfp y.val hy heq
        have hkp : ∀ y ∈ A p, k p y ∈ P := by
          intro y hy heq
          apply hy
          apply E.injOn y.property hpE
          exact sub_eq_zero.mp heq
        have hkq : ∀ y ∈ A q, k q y ∈ P := by
          intro y hy heq
          apply hy
          apply E.injOn y.property hq.2
          exact sub_eq_zero.mp heq
        let ρ : C(Plane,Plane) := ⟨fun v => H.finalMap (v+E p) - H.finalMap (E p),by
          unfold AmbientIsotopy.finalMap
          fun_prop⟩
        have hρ : ∀ v ∈ P, ρ v ∈ P := by
          intro v hv heq
          apply hv
          obtain ⟨r,hr⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
          have hh : r (v+E p) = r (E p) := by
            rw [hr,hr]
            exact sub_eq_zero.mp heq
          exact add_right_cancel (show v+E p = (0 : Plane)+E p by simpa only [zero_add] using r.injective hh)
        have hρid := moving_center_identity H (E p) ρ (fun v => rfl) hρ
        let i := ReflectionGermProof.inclusion W
        let ip := pairRelativeHomologyMap (A p) ({p}ᶜ : Set S) i (fun y hy => hy) 2
        haveI : IsIso ip := ReflectionGermProof.inclusion_isIso ({p}ᶜ : Set S) W
          (ReflectionGermProof.puncture_excision p W E.open_source hpE)
        let vp := (asIso ip).inv (homologyToRelative S ({p}ᶜ : Set S) 2 z)
        let vq := pairRelativeHomologyMap (A p) (A q) g hgp 2 vp
        have hvp : ip vp = homologyToRelative S ({p}ᶜ : Set S) 2 z :=
          (asIso ip).inv_hom_id_apply _
        refine ⟨vp,vq,hvp,?_,hkp,hkq,?_⟩
        · let K : ContinuousMap.Homotopy (ContinuousMap.id S) f := {
            toContinuousMap := G.map
            map_zero_left := G.at_zero
            map_one_left := fun y => (he y).symm }
          have hh := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
            (show TopCat.Homotopy (𝟙 (TopCat.of S)) (TopCat.ofHom f) from K)
              (ModuleCat.of ℤ ℤ) 2
          let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
            (ModuleCat.of ℤ ℤ)
          change F.map (𝟙 (TopCat.of S)) = F.map (TopCat.ofHom f) at hh
          rw [CategoryTheory.Functor.map_id] at hh
          have hn := pairRelativeHomologyMap_commutes ({p}ᶜ : Set S) ({q}ᶜ : Set S) f hfp 2
          change homologyToRelative S ({p}ᶜ : Set S) 2 ≫
            pairRelativeHomologyMap ({p}ᶜ : Set S) ({q}ᶜ : Set S) f hfp 2 =
              F.map (TopCat.ofHom f) ≫ homologyToRelative S ({q}ᶜ : Set S) 2 at hn
          rw [←hh,Category.id_comp] at hn
          have heq : f.comp i = i.comp g := by apply ContinuousMap.ext; intro y; rfl
          have hd : ip ≫ pairRelativeHomologyMap ({p}ᶜ : Set S) ({q}ᶜ : Set S) f hfp 2 =
            pairRelativeHomologyMap (A p) (A q) g hgp 2 ≫
              pairRelativeHomologyMap (A q) ({q}ᶜ : Set S) i (fun y hy => hy) 2 := by
            rw [←pairRelativeHomologyMap_comp,←pairRelativeHomologyMap_comp]
            exact ReflectionGermProof.pairMap_congr _ _ _ _ _ _ heq 2
          have hv := congrArg (fun a => a vp) hd
          change pairRelativeHomologyMap ({p}ᶜ : Set S) ({q}ᶜ : Set S) f hfp 2 (ip vp) =
            pairRelativeHomologyMap (A q) ({q}ᶜ : Set S) i (fun y hy => hy) 2 vq at hv
          rw [hvp] at hv
          have hz := congrArg (fun a => a z) hn
          exact hv.symm.trans hz
        · have heq : ρ.comp (k p) = (k q).comp g := by
            apply ContinuousMap.ext
            intro y
            change H.finalMap ((E y.val-E p)+E p) - H.finalMap (E p) = E (f y.val)-E q
            rw [sub_add_cancel,hpqplane]
            have hh := (hcoord ⟨1,by norm_num⟩ y.val y.property).2
            change E (G.finalMap y.val) = H.finalMap (E y.val) at hh
            rw [←hh]
            exact congrArg (fun v => E v - E q) (he y.val).symm
          have hd : pairRelativeHomologyMap (A p) P (k p) hkp 2 ≫
              pairRelativeHomologyMap P P ρ hρ 2 =
            pairRelativeHomologyMap (A p) (A q) g hgp 2 ≫
              pairRelativeHomologyMap (A q) P (k q) hkq 2 := by
            rw [←pairRelativeHomologyMap_comp,←pairRelativeHomologyMap_comp]
            exact ReflectionGermProof.pairMap_congr _ _ _ _ _ _ heq 2
          rw [hρid,Category.comp_id] at hd
          exact congrArg (fun a => a vp) hd
      have centered_chart_iso {S V : Type} [TopologicalSpace S] [T1Space S]
          [NormedAddCommGroup V] (E : OpenPartialHomeomorph S V) (x : S) (hx : x ∈ E.source) :
          let W := E.source
          let A : Set W := {y | y.val ≠ x}
          let P : Set V := {0}ᶜ
          let k : C(W,V) := ⟨fun y => E y.val - E x,
            (E.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
          ∀ hpres : ∀ y ∈ A, k y ∈ P,
            IsIso (pairRelativeHomologyMap A P k hpres 2) := by
        dsimp only
        intro hpres
        let W := E.source
        let A : Set W := {y | y.val ≠ x}
        let P : Set V := {0}ᶜ
        let k : C(W,V) := ⟨fun y => E y.val - E x,
          (E.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
        let e := E.transHomeomorph (Homeomorph.subRight (E x))
        have hex : e x = 0 := by change E x - E x = 0; exact sub_self _
        let B := e.target
        let D : Set B := {z | z.val ≠ 0}
        let c : W ≃ₜ B := e.toHomeomorphSourceTarget
        have hc : ∀ y ∈ A, c y ∈ D := by
          intro y hy heq
          apply hy
          exact e.injOn y.property hx (heq.trans hex.symm)
        have hci : ∀ z ∈ D, c.symm z ∈ A := by
          intro z hz heq
          apply hz
          have hh := congrArg e heq
          change e (e.symm z.val) = e x at hh
          rw [e.right_inv z.property,hex] at hh
          exact hh
        let ch : C(W,B) := ⟨c,c.continuous⟩
        let j := ReflectionGermProof.inclusion B
        have hj : ∀ z ∈ D, j z ∈ P := fun z hz => hz
        haveI : IsIso (pairRelativeHomologyMap A D ch hc 2) :=
          ReflectionGermProof.pairHomeo_isIso A D c hc hci 2
        have h0B : (0 : V) ∈ B := hex ▸ e.map_source hx
        haveI : IsIso (pairRelativeHomologyMap D P j hj 2) :=
          ReflectionGermProof.inclusion_isIso P B
            (ReflectionGermProof.puncture_excision (0 : V) B e.open_target h0B)
        have hcomp : ∀ y ∈ A, (j.comp ch) y ∈ P := fun y hy => hj _ (hc y hy)
        have heq : k = j.comp ch := by apply ContinuousMap.ext; intro y; rfl
        rw [ReflectionGermProof.pairMap_congr A P k (j.comp ch) hpres hcomp heq 2,
          pairRelativeHomologyMap_comp A D P ch j hc hj 2]
        infer_instance
      dsimp only
      let W := E.source
      let A (x : W) : Set W := {y | y.val ≠ x.val}
      let P : Set Plane := {0}ᶜ
      let k (x : W) : C(W,Plane) := ⟨fun y => E y.val - E x.val,
        (E.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
      let i (x : W) := pairRelativeHomologyMap (A x) ({x.val}ᶜ : Set S)
        (ReflectionGermProof.inclusion W) (fun y hy => hy) 2
      have hi (x : W) : IsIso (i x) :=
        ReflectionGermProof.inclusion_isIso ({x.val}ᶜ : Set S) W
          (ReflectionGermProof.puncture_excision x.val W E.open_source x.property)
      have hk (x : W) : ∀ y ∈ A x, k x y ∈ P := by
        intro y hy heq
        exact hy (E.injOn y.property x.property (sub_eq_zero.mp heq))
      let K (x : W) := pairRelativeHomologyMap (A x) P (k x) (hk x) 2
      have hK (x : W) : IsIso (K x) := centered_chart_iso E x.val x.property (hk x)
      let v (x : W) : relativeHomology W (A x) 2 :=
        letI := hi x
        (asIso (i x)).inv (homologyToRelative S ({x.val}ᶜ : Set S) 2 z)
      have hv (x : W) : i x (v x) = homologyToRelative S ({x.val}ᶜ : Set S) 2 z := by
        letI := hi x
        exact (asIso (i x)).inv_hom_id_apply _
      let n (x : W) : ℤ := φ.hom (K x (v x))
      have hn : IsLocallyConstant n := by
        rw [IsLocallyConstant.iff_eventually_eq]
        intro x
        obtain ⟨U,hU,hxU,hUs,hclasses⟩ := moving_chart_classes S x.val E x.property
        filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds hxU] with y hy
        obtain ⟨vx,vy,hvx,hvy,hpx,hpy,hxy⟩ := hclasses y.val hy z
        have heqx : vx = v x := by
          letI := hi x
          apply (ModuleCat.mono_iff_injective (i x)).mp inferInstance
          exact hvx.trans (hv x).symm
        have heqy : vy = v y := by
          letI := hi y
          apply (ModuleCat.mono_iff_injective (i y)).mp inferInstance
          exact hvy.trans (hv y).symm
        rw [heqx,heqy] at hxy
        exact congrArg φ.hom hxy.symm
      refine ⟨n,hn,?_⟩
      intro x
      refine ⟨v x,hk x,hv x,rfl,?_⟩
      letI := hi x
      letI := hK x
      have hiinj := (ModuleCat.mono_iff_injective (i x)).mp inferInstance
      have hkinj := (ModuleCat.mono_iff_injective (K x)).mp inferInstance
      constructor
      · intro hzero
        have hkzero : K x (v x) = 0 := φ.toLinearEquiv.injective (by
          change φ.hom (K x (v x)) = φ.hom 0
          rw [map_zero]
          exact hzero)
        have hvzero : v x = 0 := hkinj (by rw [map_zero]; exact hkzero)
        have hx := hv x
        rw [hvzero,map_zero] at hx
        exact hx.symm
      · intro hxzero
        have hvzero : v x = 0 := hiinj (by rw [map_zero,hv x,hxzero])
        change φ.hom (K x (v x)) = 0
        rw [hvzero,map_zero,map_zero]
    classical
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    obtain ⟨_,z,hz,hlocal⟩ := actual_genus_two_local_orientation_class M
    obtain ⟨φ⟩ := plane_local_integer_iso
    refine ⟨z,hz,hlocal,φ,?_⟩
    intro e
    obtain ⟨n,hn,hcoeff⟩ := chart_integer_section E e φ z
    refine ⟨n,hn,?_⟩
    intro x
    obtain ⟨v,hpres,hv,hc,hzero⟩ := hcoeff x
    exact ⟨fun hx => hlocal x.val (hzero.mp hx),v,hpres,hv,hc⟩

  obtain ⟨z,hz,hlocal,φ,hsections⟩ := plane_sections M
  let ep : Plane ≃ₜ ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans Homeomorph.finTwoArrow
  let ψ : ℂ ≃ₜ Plane := Complex.equivRealProdCLM.toHomeomorph.trans ep.symm
  have hψ0 : ψ 0 = 0 := by ext i; fin_cases i <;> rfl
  have hψsub (a b : ℂ) : ψ (a-b) = ψ a - ψ b := by ext i; fin_cases i <;> rfl
  let Q : Set Plane := {0}ᶜ
  let P : Set ℂ := {0}ᶜ
  let j : C(ℂ,Plane) := ⟨ψ,ψ.continuous⟩
  have hj : ∀ y ∈ P, j y ∈ Q := by
    intro y hy hh
    exact hy (ψ.injective (hh.trans hψ0.symm))
  have hji : ∀ y ∈ Q, ψ.symm y ∈ P := by
    intro y hy hh
    apply hy
    change y = 0
    simpa only [ψ.apply_symm_apply] using (congrArg ψ hh).trans hψ0
  haveI : IsIso (pairRelativeHomologyMap P Q j hj 2) :=
    ReflectionGermProof.pairHomeo_isIso P Q ψ hj hji 2
  let Φ := asIso (pairRelativeHomologyMap P Q j hj 2) ≪≫ φ
  refine ⟨z,hz,hlocal,Φ,?_⟩
  intro e
  let d := e.transHomeomorph ψ
  obtain ⟨n,hn,hcoeff⟩ := hsections d
  refine ⟨n,hn,?_⟩
  intro x
  obtain ⟨hnz,v,hkp,hv,hc⟩ := hcoeff x
  let k : C(e.source,ℂ) := ⟨fun y => e y.val-e x.val,
    (e.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
  let kp : C(d.source,Plane) := ⟨fun y => d y.val-d x.val,
    (d.continuousOn.comp_continuous continuous_subtype_val (fun y => y.property)).sub continuous_const⟩
  have hk : ∀ y ∈ {y : e.source | y.val ≠ x.val}, k y ∈ P := by
    intro y hy hh
    exact hy (e.injOn y.property x.property (sub_eq_zero.mp hh))
  refine ⟨hnz,v,hk,hv,?_⟩
  have heq : kp = j.comp k := by
    apply ContinuousMap.ext
    intro y
    exact (hψsub (e y.val) (e x.val)).symm
  have hm : pairRelativeHomologyMap _ Q kp hkp 2 =
      pairRelativeHomologyMap _ P k hk 2 ≫ pairRelativeHomologyMap P Q j hj 2 := by
    rw [←pairRelativeHomologyMap_comp]
    exact ReflectionGermProof.pairMap_congr _ _ _ _ _ _ heq 2
  rw [hc]
  change φ.hom (pairRelativeHomologyMap _ Q kp hkp 2 v) =
    φ.hom (pairRelativeHomologyMap P Q j hj 2 (pairRelativeHomologyMap _ P k hk 2 v))
  exact congrArg (fun t => φ.hom (t v)) hm
end CurveComplex.Hyperbolic
