import CurveComplexGenusTwo.Hyperbolic.Cayley
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Topology.LocalOrientation.LocalReflectionGerm
open Set Topology unitInterval
open scoped MatrixGroups ComplexConjugate
open CategoryTheory CategoryTheory.Limits
open CurveComplex CurveComplexGenusTwo.CWHurewicz CurveComplex.GenusOrientationCandidate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace CurveComplex.Hyperbolic
theorem positive_chart_coefficients_force_positive_mobius_transition {S : Type} [TopologicalSpace S] [T1Space S]
    (e d : OpenPartialHomeomorph S ℂ) (x : S) (he : x ∈ e.source) (hd : x ∈ d.source)
    (g : GL (Fin 2) ℝ)
    (hcoord : ∀ y ∈ e.source ∩ d.source,
      let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
      D (g • D.symm (e y)) = d y)
    (z : H S 2) (φ : relativeHomology ℂ ({0}ᶜ : Set ℂ) 2 ≅ ModuleCat.of ℤ ℤ) :
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
  have negative_degree (g : GL (Fin 2) ℝ) (hneg : g.val.det < 0) (p : ℂ)
      (f : C(ℂ,ℂ))
      (hf : ∀ z : ℂ,
        let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
        f z = D (g • D.symm (z+p)) - D (g • D.symm p))
      (hpres : ∀ z ∈ ({0}ᶜ : Set ℂ), f z ∈ ({0}ᶜ : Set ℂ)) :
      pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) f hpres 2 =
        -(𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2)) := by
    have positive_degree (g : GL (Fin 2) ℝ) (hpos : 0 < g.val.det) (p : ℂ)
        (f : C(ℂ,ℂ))
        (hf : ∀ z : ℂ,
          let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
          f z = D (g • D.symm (z+p)) - D (g • D.symm p))
        (hpres : ∀ z ∈ ({0}ᶜ : Set ℂ), f z ∈ ({0}ᶜ : Set ℂ)) :
        pairRelativeHomologyMap ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ) f hpres 2 =
          𝟙 (relativeHomology ℂ ({0}ᶜ : Set ℂ) 2) := by
      have positive_isotopy (g : GL (Fin 2) ℝ) (hpos : 0 < g.val.det) :
          let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
          ∃ H : AmbientIsotopy ℂ, ∀ z : H2, H.finalMap (D z) = D (g • z) := by
        have cayley_rotation (g : GL (Fin 2) ℝ) (hpos : 0 < g.val.det)
            (hI : g • UpperHalfPlane.I = UpperHalfPlane.I) :
            ∃ u : Circle, ∀ z : H2,
              (cayleyOpen (g • z) : ℂ) = (u : ℂ) * (cayleyOpen z : ℂ) := by
          have hab := (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos hpos).mp hI
          let a : ℝ := g 0 0
          let c : ℝ := g 1 0
          let d : ℂ := (a : ℂ) + (c : ℂ) * Complex.I
          have hd : d ≠ 0 := by
            intro he
            have ha := congrArg Complex.re he
            have hc := congrArg Complex.im he
            simp [d] at ha hc
            have hp := hpos
            change 0 < Matrix.det g.val at hp
            rw [Matrix.det_fin_two,←hab.1,hab.2] at hp
            change 0 < a * a - (-c) * c at hp
            rw [ha,hc] at hp
            norm_num at hp
          have hn : (a : ℂ) - (c : ℂ) * Complex.I = conj d := by simp [d,sub_eq_add_neg]
          have hnorm : ‖((a : ℂ) - (c : ℂ) * Complex.I) / d‖ = 1 := by
            rw [hn,norm_div,Complex.norm_conj,div_self (norm_ne_zero_iff.mpr hd)]
          let u : Circle := ⟨((a : ℂ) - (c : ℂ) * Complex.I) / d,
            by
              change dist (((a : ℂ) - (c : ℂ) * Complex.I) / d) 0 = 1
              simpa only [dist_zero_right] using hnorm⟩
          refine ⟨u,?_⟩
          intro z
          have hz : (z : ℂ) + Complex.I ≠ 0 := by
            intro he
            have hi : 0 < (z : ℂ).im := z.im_pos
            have hh := congrArg Complex.im he
            simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at hh
            linarith
          have hgz : ((g • z : H2) : ℂ) + Complex.I ≠ 0 := by
            intro he
            have hi : 0 < ((g • z : H2) : ℂ).im := (g • z : H2).im_pos
            have hh := congrArg Complex.im he
            simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at hh
            linarith
          have hformula : ((g • z : H2) : ℂ) =
              ((a : ℂ) * (z : ℂ) - (c : ℂ)) / ((c : ℂ) * (z : ℂ) + (a : ℂ)) := by
            rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
            simp only [UpperHalfPlane.num,UpperHalfPlane.denom,←hab.1,hab.2,Complex.ofReal_neg]
            rfl
          have hden : (c : ℂ) * (z : ℂ) + (a : ℂ) ≠ 0 := by
            simpa only [UpperHalfPlane.denom,←hab.1] using UpperHalfPlane.denom_ne_zero g z
          change (((g • z : H2) : ℂ) - Complex.I) / (((g • z : H2) : ℂ) + Complex.I) =
            (((a : ℂ) - (c : ℂ) * Complex.I) / d) * (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I))
          apply (div_eq_iff hgz).mpr
          rw [hformula]
          dsimp only [d] at hd ⊢
          have hden' : (a : ℂ) + (z : ℂ) * (c : ℂ) ≠ 0 := by
            simpa only [add_comm,mul_comm] using hden
          field_simp [hd,hz,hden,hden']
          ring_nf
          field_simp [hden']
          ring_nf
          have hI3 : Complex.I ^ 3 = -Complex.I := by norm_num [pow_succ,Complex.I_sq]
          simp only [Complex.I_sq,hI3]
          ring
        let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
        let q : H2 := g • UpperHalfPlane.I
        let a := q.toSL2R
        let A : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ a
        let b : GL (Fin 2) ℝ := A⁻¹ * g
        have hAI : A • UpperHalfPlane.I = q := by
          change a • UpperHalfPlane.I = q
          exact q.toSL2R_smul_I
        have hdetA : A.det = 1 := by simp [A]
        have hposb : 0 < b.val.det := by
          change 0 < b.det.val
          have hh : 0 < g.det.val := hpos
          simpa only [b,map_mul,map_inv,hdetA,inv_one,one_mul] using hh
        have hbI : b • UpperHalfPlane.I = UpperHalfPlane.I := by
          change (A⁻¹ * g) • UpperHalfPlane.I = UpperHalfPlane.I
          rw [mul_smul]
          change A⁻¹ • q = UpperHalfPlane.I
          rw [←hAI,inv_smul_smul]
        obtain ⟨u,hu⟩ := cayley_rotation b hposb hbI
        have hDrot (z : H2) : D (b • z) = (u : ℂ) * D z := by
          change (Real.sqrt (1 - ‖(cayleyOpen (b • z) : ℂ)‖ ^ 2))⁻¹ •
              (cayleyOpen (b • z) : ℂ) = (u : ℂ) *
                ((Real.sqrt (1 - ‖(cayleyOpen z : ℂ)‖ ^ 2))⁻¹ • (cayleyOpen z : ℂ))
          rw [hu,norm_mul,Circle.norm_coe,one_mul]
          simp only [Complex.real_smul]
          ring
        have ha0 : a 1 0 = 0 := by simp [a,UpperHalfPlane.toSL2R]
        obtain ⟨s,r,har⟩ := UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_eq_zero a ha0
        let γ : Path (1 : Circle) u := PathConnectedSpace.somePath 1 u
        let st (t : unitInterval) : {s : ℝ // 0 < s} :=
          ⟨Real.exp ((t : ℝ) * Real.log s.val),Real.exp_pos _⟩
        let et (t : unitInterval) : H2 ≃ᵢ H2 := {
          toEquiv := {
            toFun := fun z => ((t : ℝ)*r) +ᵥ (st t • z)
            invFun := fun z => (st t)⁻¹ • (-((t : ℝ)*r) +ᵥ z)
            left_inv := fun z => by simp only [neg_vadd_vadd,inv_smul_smul]
            right_inv := fun z => by simp only [smul_inv_smul,vadd_neg_vadd] }
          isometry_toFun := (UpperHalfPlane.isometry_real_vadd ((t : ℝ)*r)).comp
            (UpperHalfPlane.isometry_pos_mul (st t)) }
        let F (t : unitInterval) (z : ℂ) := D (et t (D.symm ((γ t : ℂ)*z)))
        have hF : Continuous (fun p : unitInterval × ℂ => F p.1 p.2) := by
          apply D.continuous.comp
          apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
          change Continuous (fun p : unitInterval × ℂ =>
            (((p.1 : ℝ)*r : ℝ) : ℂ) +
              Real.exp ((p.1 : ℝ)*Real.log s.val) • (D.symm ((γ p.1 : ℂ)*p.2) : ℂ))
          fun_prop
        let H : AmbientIsotopy ℂ := {
          map := ⟨fun p => F p.1 p.2,hF⟩
          homeomorphism_at := by
            intro t
            exact ⟨((Homeomorph.mulLeft₀ (γ t : ℂ) (γ t).coe_ne_zero).trans D.symm).trans
              ((et t).toHomeomorph.trans D),fun z => rfl⟩
          at_zero := by
            intro z
            change D (et (⟨0,by norm_num⟩ : unitInterval) (D.symm ((γ 0 : ℂ)*z))) = z
            simp only [γ.source,Circle.coe_one,one_mul]
            have hst : st (⟨0,by norm_num⟩ : unitInterval) = 1 := by
              apply Subtype.ext
              simp [st]
            change D ((((0 : ℝ)*r) +ᵥ ((st 0) • D.symm z))) = z
            rw [show st 0 = 1 from hst]
            simp }
        refine ⟨H,?_⟩
        intro z
        change D (et 1 (D.symm ((γ 1 : ℂ)*D z))) = D (g • z)
        rw [γ.target,←hDrot,D.symm_apply_apply]
        have hst : st 1 = s := by
          apply Subtype.ext
          simp [st,Real.exp_log s.property]
        change D (((1 : ℝ)*r) +ᵥ (st 1 • (b • z))) = D (g • z)
        rw [hst,one_mul]
        have hh := congrFun har (b • z)
        change a • (b • z) = r +ᵥ (s • (b • z)) at hh
        rw [←hh]
        change D (A • (b • z)) = D (g • z)
        change D (A • ((A⁻¹ * g) • z)) = D (g • z)
        rw [mul_smul,smul_inv_smul]
      have moving_identity {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (H : AmbientIsotopy V) (p : V)
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
      let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
      obtain ⟨H,hH⟩ := positive_isotopy g hpos
      apply moving_identity H p f _ hpres
      intro z
      rw [hf z]
      have h1 := hH (D.symm (z+p))
      have h0 := hH (D.symm p)
      rw [D.apply_symm_apply] at h1 h0
      exact congrArg₂ (fun a b : ℂ => a-b) h1.symm h0.symm
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
    let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
    have hDJ (z : H2) : D (UpperHalfPlane.J • z) = star (D z) := by
      have hC : (cayleyOpen (UpperHalfPlane.J • z) : ℂ) = star (cayleyOpen z : ℂ) := by
        change (((UpperHalfPlane.J • z : H2) : ℂ)-Complex.I) /
            (((UpperHalfPlane.J • z : H2) : ℂ)+Complex.I) =
          star (((z : ℂ)-Complex.I)/((z : ℂ)+Complex.I))
        rw [UpperHalfPlane.coe_J_smul]
        simp only [Complex.star_def,map_div₀,map_sub,map_add,Complex.conj_I]
        rw [show -conj (z : ℂ)-Complex.I = -(conj (z : ℂ)+Complex.I) by ring,
          show -conj (z : ℂ)+Complex.I = -(conj (z : ℂ)-Complex.I) by ring]
        simpa only [sub_neg_eq_add,sub_eq_add_neg,neg_neg] using
          neg_div_neg_eq (conj (z : ℂ)+Complex.I) (conj (z : ℂ)-Complex.I)
      change (Real.sqrt (1-‖(cayleyOpen (UpperHalfPlane.J • z) : ℂ)‖^2))⁻¹ •
          (cayleyOpen (UpperHalfPlane.J • z) : ℂ) =
        star ((Real.sqrt (1-‖(cayleyOpen z : ℂ)‖^2))⁻¹ • (cayleyOpen z : ℂ))
      rw [hC,norm_star]
      simp only [Complex.real_smul,Complex.star_def,map_mul,Complex.conj_ofReal]
    have hDsymm (w : ℂ) : D.symm (star w) = UpperHalfPlane.J • D.symm w := by
      apply D.injective
      rw [D.apply_symm_apply,hDJ,D.apply_symm_apply]
    have hJJ (z : H2) : UpperHalfPlane.J • (UpperHalfPlane.J • z) = z := by
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.coe_J_smul]
    let b := g * UpperHalfPlane.J
    have hpos : 0 < b.val.det := by
      change 0 < (g*UpperHalfPlane.J).det.val
      rw [map_mul,UpperHalfPlane.det_J]
      simpa using neg_pos.mpr hneg
    have haction (w : ℂ) : D (g • D.symm w) = D (b • D.symm (star w)) := by
      rw [hDsymm]
      change D (g • D.symm w) = D ((g*UpperHalfPlane.J) • (UpperHalfPlane.J • D.symm w))
      rw [mul_smul,hJJ]
    let F : C(ℂ,ℂ) := ⟨fun w => D (b • D.symm (w+star p)) - D (b • D.symm (star p)),by fun_prop⟩
    have hF : ∀ w ∈ ({0}ᶜ : Set ℂ), F w ∈ ({0}ᶜ : Set ℂ) := by
      intro w hw hh
      apply hw
      have hh' := D.injective (sub_eq_zero.mp hh)
      have hpoints := D.symm.injective (MulAction.injective b hh')
      exact add_right_cancel (show w+star p = (0 : ℂ)+star p by simpa only [zero_add] using hpoints)
    have hpositive := positive_degree b hpos (star p) F (fun w => rfl) hF
    let c : C(ℂ,ℂ) := ⟨star,continuous_star⟩
    have hc : ∀ w ∈ ({0}ᶜ : Set ℂ), c w ∈ ({0}ᶜ : Set ℂ) := by
      intro w hw hh
      exact hw (star_eq_zero.mp hh)
    have heq : f = F.comp c := by
      apply ContinuousMap.ext
      intro w
      rw [hf w,haction (w+p),haction p]
      change D (b • D.symm (star (w+p))) - D (b • D.symm (star p)) =
        D (b • D.symm (star w+star p)) - D (b • D.symm (star p))
      rw [star_add]
    have hcomp : ∀ w ∈ ({0}ᶜ : Set ℂ), (F.comp c) w ∈ ({0}ᶜ : Set ℂ) :=
      fun w hw => hF _ (hc w hw)
    rw [ReflectionGermProof.pairMap_congr _ _ f (F.comp c) hpres hcomp heq 2,
      pairRelativeHomologyMap_comp _ _ _ c F hc hF 2,hpositive,conjugation_degree hc]
    exact Category.comp_id _
  have overlap_transport {S : Type} [TopologicalSpace S] [T1Space S]
      (e d : OpenPartialHomeomorph S ℂ) (x : S) (he : x ∈ e.source) (hd : x ∈ d.source)
      (z : H S 2) :
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
  dsimp only
  intro v w hk hl hv hw ha hb
  by_contra hn
  have hdet : g.val.det ≠ 0 := g.det_ne_zero
  have hneg : g.val.det < 0 := lt_of_le_of_ne (le_of_not_gt hn) hdet
  let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
  let F : C(ℂ,ℂ) := ⟨fun t => D (g • D.symm (t+e x))-D (g • D.symm (e x)),by fun_prop⟩
  have hF : ∀ t ∈ ({0}ᶜ : Set ℂ), F t ∈ ({0}ᶜ : Set ℂ) := by
    intro t ht hh
    apply ht
    have h := D.symm.injective (MulAction.injective g (D.injective (sub_eq_zero.mp hh)))
    exact add_right_cancel (show t+e x = (0 : ℂ)+e x by simpa only [zero_add] using h)
  have hc : ∀ y ∈ e.source ∩ d.source, F (e y-e x) = d y-d x := by
    intro y hy
    change D (g • D.symm ((e y-e x)+e x))-D (g • D.symm (e x)) = d y-d x
    rw [sub_add_cancel,hcoord y hy,hcoord x ⟨he,hd⟩]
  have ht := overlap_transport e d x he hd z v w hk hl hv hw F hF hc
  have hnegative := negative_degree g hneg (e x) F (fun t => rfl) hF
  rw [hnegative] at ht
  have heq : φ.hom (pairRelativeHomologyMap _ _ _ hl 2 w) =
      -φ.hom (pairRelativeHomologyMap _ _ _ hk 2 v) := by
    rw [ht]
    simp
  rw [heq] at hb
  exact (not_lt_of_ge (neg_nonpos.mpr ha.le)) hb
end CurveComplex.Hyperbolic
