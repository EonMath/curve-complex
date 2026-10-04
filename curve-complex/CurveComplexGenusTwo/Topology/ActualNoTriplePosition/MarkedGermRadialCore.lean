import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedInteriorContactFanPreprocessing
import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.ScaleNormalizedChart

namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem hMarkedGermRadialCore (M : HyperellipticModel E S) {I : Type} [Fintype I]
      (c : I → EssentialMarkedArc M) (p : S)
      (E0 : OpenPartialHomeomorph S Plane) (hEp : E0 p=0)
      (U : Set S) (hU : IsOpen U) (hpU : p ∈ U) (hUE : U ⊆ E0.source)
      (g : I × Bool → Interval → S)
      (hg : ∀ j, IsClosedEmbedding (g j) ∧ g j 0=p ∧ range (g j) ⊆ U)
      (hmeet : ∀ i j, i ≠ j → range (g i) ∩ range (g j)={p})
      (K : I → Set S) (hK : ∀ i, IsCompact (K i) ∧ p ∉ K i ∧
        (c i).val.image=range (g (i,false)) ∪ range (g (i,true)) ∪ K i)
      (i0 : I) :
      let γ : I × Bool → Interval → Plane := fun j => E0 ∘ g j
      ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E0 '' U),
        R.vector (i0,true) = -R.vector (i0,false) ∧
        ∀ i x, x ∈ E0.source → ‖R.H (E0 x)‖ ≤ R.coreRadius →
          (x ∈ (c i).val.image ↔ R.H (E0 x) ∈
            segment ℝ (0:Plane) (R.vector (i,false)) ∪
            segment ℝ (0:Plane) (R.vector (i,true))) := by
    letI : T2Space S := M.sphere.symm.t2Space
    let γ : I × Bool → Interval → Plane := fun j => E0 ∘ g j
    have hsource (j : I × Bool) (t : Interval) : g j t ∈ E0.source :=
      hUE ((hg j).2.2 (Set.mem_range_self t))
    have hγ (j : I × Bool) : IsClosedEmbedding (γ j) := by
      have hc : Continuous (γ j) := E0.continuousOn.comp_continuous (hg j).1.continuous
        (fun t => hsource j t)
      apply hc.isClosedEmbedding
      intro t u he
      exact (hg j).1.injective (E0.injOn (hsource j t) (hsource j u) he)
    have hγ0 (j : I × Bool) : γ j 0=0 := by
      change E0 (g j 0)=0
      rw [(hg j).2.1,hEp]
    have hγmeet (i j : I × Bool) (hij : i ≠ j) : range (γ i) ∩ range (γ j)={0} := by
      ext x
      constructor
      · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
        have he := E0.injOn (hsource i t) (hsource j u) (ht.trans hu.symm)
        have hp : g i t=p := by
          have hh : g i t ∈ range (g i) ∩ range (g j) := ⟨⟨t,rfl⟩,⟨u,he.symm⟩⟩
          rw [hmeet i j hij] at hh
          exact hh
        exact Set.mem_singleton_iff.mpr (ht.symm.trans ((congrArg E0 hp).trans hEp))
      · rintro rfl
        exact ⟨⟨0,hγ0 i⟩,⟨0,hγ0 j⟩⟩
    let bad : Set S := ⋃ i, K i
    have hBad : IsClosed bad := isClosed_iUnion_of_finite (fun i => (hK i).1.isClosed)
    have hpBad : p ∉ bad := by
      intro hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      exact (hK i).2.1 hi
    let W := U \ bad
    have hW : IsOpen W := hU.sdiff hBad
    have hpW : p ∈ W := ⟨hpU,hpBad⟩
    have hWE : W ⊆ E0.source := fun x hx => hUE hx.1
    have hPlaneW : IsOpen (E0 '' W) := E0.isOpen_image_of_subset_source hW hWE
    have hzeroW : (0:Plane) ∈ E0 '' W := ⟨p,hpW,hEp⟩
    obtain ⟨R0,hRop⟩ := prescribed_pair_finite_actual_star_radialization_zero
      γ hγ hγ0 hγmeet (i0,false) (i0,true) (by simp) (E0 '' W) hPlaneW hzeroW
    let R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E0 '' U) := {R0 with
      support_subset := R0.support_subset.trans (Set.image_mono Set.diff_subset)}
    have hNotK (i : I) (x : S) (hxE : x ∈ E0.source)
        (hxN : ‖R.H (E0 x)‖ ≤ R.coreRadius) : x ∉ K i := by
      intro hxK
      have hxPlane : E0 x ∉ E0 '' W := by
        rintro ⟨y,hy,he⟩
        have hyx : y=x := E0.injOn (hWE hy) hxE he
        exact hy.2 (hyx.symm ▸ Set.mem_iUnion.mpr ⟨i,hxK⟩)
      have hxOut : E0 x ∉ Metric.ball (0:Plane) R0.supportRadius := by
        intro hx
        exact hxPlane (R0.support_subset (Metric.ball_subset_closedBall hx))
      have hxFix : R.H (E0 x)=E0 x := R0.fixes_exterior _ hxOut
      rw [hxFix] at hxN
      have hxBall : E0 x ∈ Metric.closedBall (0:Plane) R0.supportRadius := by
        rw [Metric.mem_closedBall,dist_zero_right]
        exact hxN.trans R0.core_lt_support.le
      exact hxPlane (R0.support_subset hxBall)
    refine ⟨R,hRop,?_⟩
    intro i x hxE hxN
    constructor
    · intro hx
      have hxG : x ∈ range (g (i,false)) ∪ range (g (i,true)) := by
        rw [(hK i).2.2] at hx
        exact hx.resolve_right (hNotK i x hxE hxN)
      have hrecover (sign : Bool) (hxg : x ∈ range (g (i,sign))) :
          R.H (E0 x) ∈ segment ℝ (0:Plane) (R.vector (i,sign)) := by
        obtain ⟨t,ht⟩ := hxg
        have hγx : γ (i,sign) t=E0 x := congrArg E0 ht
        have hcut : t.val ≤ (R.cut (i,sign)).val := by
          by_contra hn
          have htail : R.H (γ (i,sign) t) ∈ R.H ''
              CurveComplex.FiniteStarGeometry.tail γ (i,sign) (R.cut (i,sign)) :=
            ⟨γ (i,sign) t,⟨t,(lt_of_not_ge hn).le,rfl⟩,rfl⟩
          have hball : R.H (γ (i,sign) t) ∈ Metric.closedBall (0:Plane) R.coreRadius := by
            rw [hγx,Metric.mem_closedBall,dist_zero_right]
            exact hxN
          exact Set.disjoint_left.mp (R.excludes_tails (i,sign)) htail hball
        have hh : R.H (γ (i,sign) t) ∈ R.H ''
            CurveComplex.FiniteStarGeometry.armPrefix γ (i,sign) (R.cut (i,sign)) :=
          ⟨γ (i,sign) t,⟨t,hcut,rfl⟩,rfl⟩
        simpa only [R.prefix_image,zero_add,hγx] using hh
      exact hxG.elim (fun h => Or.inl (hrecover false h)) (fun h => Or.inr (hrecover true h))
    · intro hx
      have hrecover (sign : Bool) (hray : R.H (E0 x) ∈ segment ℝ (0:Plane) (R.vector (i,sign))) :
          x ∈ (c i).val.image := by
        have hh : R.H (E0 x) ∈ R.H ''
            CurveComplex.FiniteStarGeometry.armPrefix γ (i,sign) (R.cut (i,sign)) := by
          rw [R.prefix_image,zero_add]
          exact hray
        obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hh
        have hEx : γ (i,sign) t=E0 x := R.H.injective he
        have hsx : g (i,sign) t=x := E0.injOn (hsource (i,sign) t) hxE hEx
        rw [(hK i).2.2]
        cases sign
        · exact Or.inl (Or.inl ⟨t,hsx⟩)
        · exact Or.inl (Or.inr ⟨t,hsx⟩)
      exact hx.elim (hrecover false) (hrecover true)

private theorem hMarkedNormalizeRadialCore (M : HyperellipticModel E S)
      {J : Type} [Fintype J] (c : J → EssentialMarkedArc M) (p : S)
      (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) (hEp : E p = 0)
      (γ : (J × Bool) → CurveComplex.Interval → Plane)
      (R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E '' E.source)) (j₀ : J)
      (hop : R.vector (j₀,true) = -R.vector (j₀,false)) (β : Bool)
      (hcore : ∀ j x, x ∈ E.source → ‖R.H (E x)‖ ≤ R.coreRadius →
        (x ∈ (c j).val.image ↔ R.H (E x) ∈ segment ℝ (0 : Plane) (R.vector (j,false)) ∪
          segment ℝ (0 : Plane) (R.vector (j,true)))) :
      ∃ T : Plane ≃L[ℝ] Plane, ∃ F : OpenPartialHomeomorph S Plane, ∃ ρ : ℝ,
        F.source = E.source ∧ F p = 0 ∧ 0 < ρ ∧ ρ < 1 ∧
        (∀ x, F x = T (R.H (E x))) ∧ T (R.vector (j₀,β)) = Plane.mk 1 0 ∧
        (∀ x, ‖F x‖ < ρ → ‖R.H (E x)‖ ≤ R.coreRadius) ∧
        (∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ (c j₀).val.image ↔ F x 1 = 0)) ∧
        (∀ j x, x ∈ F.source → ‖F x‖ < ρ →
          (x ∈ (c j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (T (R.vector (j,false))) ∪
            segment ℝ (0 : Plane) (T (R.vector (j,true))))) := by
    classical
    have hLinear (v : Plane) (hv : v ≠ 0) :
        ∃ T : Plane ≃L[ℝ] Plane, T v = Plane.mk 1 0 ∧
          T (-v) = Plane.mk (-1) 0 ∧ ∀ t : ℝ, T (t • v) = Plane.mk t 0 := by
      let L : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM.trans
        ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm)
      let ζ : ℂ := L.symm v
      have hζ : ζ ≠ 0 := by
        intro hz
        apply hv
        have hh := congrArg L hz
        simpa [ζ] using hh
      let M : ℂ ≃L[ℂ] ℂ := (LinearEquiv.smulOfNeZero ℂ ℂ ζ⁻¹ (inv_ne_zero hζ)).toContinuousLinearEquiv
      let T : Plane ≃L[ℝ] Plane := L.symm.trans ((M.restrictScalars ℝ).trans L)
      have hTv : T v = Plane.mk 1 0 := by
        change L (ζ⁻¹ * ζ) = Plane.mk 1 0
        rw [inv_mul_cancel₀ hζ]
        rfl
      refine ⟨T,hTv,?_,?_⟩
      · rw [map_neg,hTv]
        ext i
        fin_cases i <;> simp [Plane.mk]
      · intro t
        rw [map_smul,hTv]
        ext i
        fin_cases i <;> simp [Plane.mk]
    obtain ⟨T,hTv,hTneg,hTline⟩ := hLinear (R.vector (j₀,β)) (R.vector_nonzero (j₀,β))
    let F := E.transHomeomorph (R.H.trans T.toHomeomorph)
    have hFp : F p = 0 := by
      change T (R.H (E p)) = 0
      rw [hEp,R.fixes_center,map_zero]
    have hOpen : IsOpen (T.symm ⁻¹' Metric.ball (0 : Plane) R.coreRadius) :=
      isOpen_ball.preimage T.symm.continuous
    have h0 : (0 : Plane) ∈ T.symm ⁻¹' Metric.ball (0 : Plane) R.coreRadius := by
      change T.symm 0 ∈ Metric.ball (0 : Plane) R.coreRadius
      rw [map_zero]
      simpa using R.core_pos
    obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hOpen 0 h0
    let ρ := min r 1 / 2
    have hρ : 0 < ρ := half_pos (lt_min hr zero_lt_one)
    have hρr : ρ < r := by dsimp [ρ]; linarith [min_le_left r 1]
    have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [min_le_right r 1]
    have hCoreNorm (x : S) (hx : ‖F x‖ < ρ) : ‖R.H (E x)‖ ≤ R.coreRadius := by
      have hh : T.symm (F x) ∈ Metric.ball (0 : Plane) R.coreRadius :=
        hBall (Metric.mem_ball.mpr (by rw [dist_zero_right]; exact hx.trans hρr))
      change T.symm (T (R.H (E x))) ∈ Metric.ball (0 : Plane) R.coreRadius at hh
      rw [T.symm_apply_apply,Metric.mem_ball,dist_zero_right] at hh
      exact hh.le
    have hSegment (v z : Plane) : z ∈ segment ℝ (0 : Plane) v ↔
        T z ∈ segment ℝ (0 : Plane) (T v) := by
      have hi := image_segment ℝ T.toLinearMap.toAffineMap (0 : Plane) v
      change T '' segment ℝ (0 : Plane) v = segment ℝ (T 0) (T v) at hi
      rw [map_zero] at hi
      rw [← hi]
      exact ⟨fun hz => ⟨z,hz,rfl⟩,fun ⟨w,hw,he⟩ => (T.injective he) ▸ hw⟩
    have hModel (j : J) (x : S) (hxE : x ∈ F.source) (hxN : ‖F x‖ < ρ) :
        x ∈ (c j).val.image ↔ F x ∈ segment ℝ (0 : Plane) (T (R.vector (j,false))) ∪
          segment ℝ (0 : Plane) (T (R.vector (j,true))) := by
      rw [hcore j x hxE (hCoreNorm x hxN)]
      exact or_congr (hSegment _ _) (hSegment _ _)
    have hAxisModel (z : Plane) (hz : ‖z‖ < 1) :
        z ∈ segment ℝ (0 : Plane) (Plane.mk 1 0) ∪ segment ℝ (0 : Plane) (Plane.mk (-1) 0) ↔ z 1 = 0 := by
      constructor
      · intro hseg
        have hzero (v : Plane) (hv : v 1 = 0) (hz : z ∈ segment ℝ (0 : Plane) v) : z 1 = 0 := by
          rw [segment_eq_image'] at hz
          obtain ⟨t,ht,he⟩ := hz
          have hh := congrArg (fun z : Plane => z 1) he
          change 0+t*(v 1-0) = z 1 at hh
          rw [hv] at hh
          simpa using hh.symm
        exact hseg.elim (hzero _ rfl) (hzero _ rfl)
      · intro hz1
        have hxabs : |z 0| < 1 := (show ‖z 0‖ ≤ ‖z‖ from PiLp.norm_apply_le z 0).trans_lt hz
        by_cases hx : 0 ≤ z 0
        · left
          rw [segment_eq_image']
          refine ⟨z 0,⟨hx,(abs_lt.mp hxabs).2.le⟩,?_⟩
          ext i
          fin_cases i <;> simp [Plane.mk,hz1]
        · right
          rw [segment_eq_image']
          refine ⟨-z 0,⟨by linarith,(by linarith [(abs_lt.mp hxabs).1])⟩,?_⟩
          ext i
          fin_cases i <;> simp [Plane.mk,hz1]
    refine ⟨T,F,ρ,rfl,hFp,hρ,hρ1,(fun _ => rfl),hTv,hCoreNorm,?_,hModel⟩
    intro x hxE hxN
    cases β
    · rw [hModel j₀ x hxE hxN,hop,hTv,hTneg]
      exact hAxisModel _ (hxN.trans hρ1)
    · have hrev : R.vector (j₀,false) = -R.vector (j₀,true) := by rw [hop,neg_neg]
      rw [hModel j₀ x hxE hxN,hrev,hTneg,hTv,Set.union_comm]
      exact hAxisModel _ (hxN.trans hρ1)

private theorem hMarkedCrossingCannotStayInHalf (M : HyperellipticModel E S)
      (c d : EssentialMarkedArc M) (p : S) (hc : CrossesInDisk M c d p)
      (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) (hEp : E p = 0)
      (ρ σ : ℝ) (hρ : 0 < ρ)
      (haxis : ∀ x ∈ E.source, ‖E x‖ < ρ → (x ∈ c.val.image ↔ E x 1 = 0))
      (hhalf : ∀ x ∈ E.source, ‖E x‖ < ρ → x ∈ d.val.image → x ≠ p → 0 < σ * E x 1) : False := by
    classical
    have hCrossChart : ∃ U : Set S, ∃ V : Set (ℝ × ℝ), ∃ hpU : p ∈ U,
        ∃ h : U ≃ₜ V, IsOpen U ∧ IsOpen V ∧ (h ⟨p,hpU⟩).val=(0,0) ∧
          ∀ x (hx : x ∈ U),
            (x ∈ c.val.image ↔ (h ⟨x,hx⟩).val.1=0) ∧
            (x ∈ d.val.image ↔ (h ⟨x,hx⟩).val.2=0) := by
      obtain ⟨U,hU,hpU,hmarks,e,he0,hcA,hdA⟩ := hc
      let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
      let swap : V ≃ₜ V := (Homeomorph.prodComm ℝ ℝ).subtype (fun _ => and_comm)
      have hV : IsOpen V :=
        (isOpen_lt continuous_fst.abs continuous_const).inter
          (isOpen_lt continuous_snd.abs continuous_const)
      refine ⟨U,V,hpU,e.trans swap,hU,hV,?_,?_⟩
      · change ((e ⟨p,hpU⟩).val.2,(e ⟨p,hpU⟩).val.1)=(0,0)
        rw [he0]
      · intro x hx
        exact ⟨hcA ⟨x,hx⟩,hdA ⟨x,hx⟩⟩
    obtain ⟨U,V,hpU,h,hU,hV,hpH,haxes⟩ := hCrossChart
    have hQ : IsOpen (E.source ∩ U) := E.open_source.inter hU
    have hImageQ : IsOpen (E '' (E.source ∩ U)) := E.isOpen_image_of_subset_source hQ Set.inter_subset_left
    have h0ImageQ : (0 : Plane) ∈ E '' (E.source ∩ U) := ⟨p,⟨hpE,hpU⟩,hEp⟩
    obtain ⟨r₀,hr₀,hr₀Q⟩ := Metric.isOpen_iff.mp hImageQ 0 h0ImageQ
    let r := min r₀ ρ / 2
    have hr : 0 < r := half_pos (lt_min hr₀ hρ)
    have hrr₀ : r < r₀ := by dsimp [r]; linarith [min_le_left r₀ ρ]
    have hrρ : r < ρ := by dsimp [r]; linarith [min_le_right r₀ ρ]
    have hBallData (y : Plane) (hy : y ∈ Metric.ball (0 : Plane) r) :
        y ∈ E.target ∧ E.symm y ∈ U ∧ E.symm y ∈ E.source := by
      obtain ⟨x,hx,hxy⟩ := hr₀Q (Metric.ball_subset_ball hrr₀.le hy)
      have hyT : y ∈ E.target := hxy ▸ E.map_source hx.1
      have he : E.symm y = x := by rw [← hxy]; exact E.left_inv hx.1
      exact ⟨hyT,he ▸ hx.2,he ▸ hx.1⟩
    let P : Set Plane := Metric.ball (0 : Plane) r ∩ {y | 0 < σ * y 1}
    have hP : IsPreconnected P := (convex_ball (0 : Plane) r).inter
      (convex_halfSpace_gt (𝕜 := ℝ) (f := fun y : Plane => σ * y 1)
        ⟨by intros x y; change σ * (x 1 + y 1) = σ*x 1 + σ*y 1; ring,
         by intros a x; change σ * (a*x 1) = a*(σ*x 1); ring⟩ 0) |>.isPreconnected
    have hPU (y : P) : E.symm y.val ∈ U := (hBallData y.val y.property.1).2.1
    let Q : P → U := fun y => ⟨E.symm y.val,hPU y⟩
    have hQc : Continuous Q := (E.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun y => (hBallData y.val y.property.1).1)).subtype_mk _
    let F : P → ℝ := fun y => ((h (Q y) : V) : ℝ × ℝ).1
    have hF : Continuous F := continuous_fst.comp
      (continuous_subtype_val.comp (h.continuous.comp hQc))
    have hFne (y : P) : F y ≠ 0 := by
      intro he
      have hcX : E.symm y.val ∈ c.val.image := (haxes _ (hPU y)).1.mpr he
      have hxy : E (E.symm y.val) = y.val := E.right_inv (hBallData y.val y.property.1).1
      have hyρ : ‖E (E.symm y.val)‖ < ρ := by
        rw [hxy]
        have hh : ‖y.val‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using y.property.1
        exact hh.trans hrρ
      have hy0 := (haxis _ (hBallData y.val y.property.1).2.2 hyρ).mp hcX
      rw [hxy] at hy0
      have hh := y.property.2
      change 0 < σ * y.val 1 at hh
      rw [hy0,mul_zero] at hh
      exact (lt_irrefl 0) hh
    let O : Set V := (fun y : V => (h.symm y : S)) ⁻¹'
      (E.source ∩ E ⁻¹' Metric.ball (0 : Plane) r)
    have hO : IsOpen O := (E.isOpen_inter_preimage isOpen_ball).preimage
      (continuous_subtype_val.comp h.symm.continuous)
    have hGlobalO : IsOpen (Subtype.val '' O : Set (ℝ × ℝ)) := hV.isOpenEmbedding_subtypeVal.isOpenMap _ hO
    have h0O : ((0,0) : ℝ × ℝ) ∈ Subtype.val '' O := by
      refine ⟨h ⟨p,hpU⟩,?_,hpH⟩
      change (h.symm (h ⟨p,hpU⟩) : S) ∈ E.source ∩ E ⁻¹' Metric.ball (0 : Plane) r
      simp only [h.symm_apply_apply]
      exact ⟨hpE,by change E p ∈ Metric.ball (0 : Plane) r; rw [hEp]; simpa using hr⟩
    obtain ⟨δ,hδ,hδO⟩ := Metric.isOpen_iff.mp hGlobalO (0,0) h0O
    have hpm (s : ℝ) (hs : s = -δ/2 ∨ s = δ/2) : (s,0) ∈ Metric.ball (0 : ℝ × ℝ) δ := by
      rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        change |s-0| < δ
        rw [sub_zero]
        rcases hs with rfl | rfl <;> rw [abs_div] <;> simp [abs_of_pos hδ,abs_of_neg (neg_neg_of_pos hδ)] <;> linarith
      · simpa using hδ
    have hPoint (s : ℝ) (hs : s = -δ/2 ∨ s = δ/2) :
        ∃ y : P, F y = s := by
      obtain ⟨v,hv,hvs⟩ := hδO (hpm s hs)
      have hxE : (h.symm v : S) ∈ E.source := hv.1
      have hxBall : E (h.symm v : S) ∈ Metric.ball (0 : Plane) r := hv.2
      have hxNr : ‖E (h.symm v : S)‖ < r := by
        simpa only [Metric.mem_ball,dist_zero_right] using hxBall
      have hxN : ‖E (h.symm v : S)‖ < ρ := hxNr.trans hrρ
      have hHvalue : ((h ⟨(h.symm v : S),(h.symm v).property⟩ : V) : ℝ × ℝ) = (s,0) := by
        simpa using hvs
      have hxd : (h.symm v : S) ∈ d.val.image := (haxes _ (h.symm v).property).2.mpr (by rw [hHvalue])
      have hxp : (h.symm v : S) ≠ p := by
        intro he
        have hv0 : ((h ⟨(h.symm v : S),(h.symm v).property⟩ : V) : ℝ × ℝ) = (0,0) := by
          convert hpH using 1
          congr 2
          exact Subtype.ext he
        have hs0 : s = 0 := congrArg Prod.fst (hHvalue.symm.trans hv0)
        rcases hs with hs | hs <;> linarith
      have hxUp := hhalf _ hxE hxN hxd hxp
      let y : P := ⟨E (h.symm v : S),⟨hxBall,hxUp⟩⟩
      refine ⟨y,?_⟩
      have hQy : Q y = h.symm v := by
        apply Subtype.ext
        exact E.left_inv hxE
      change ((h (Q y) : V) : ℝ × ℝ).1 = s
      rw [hQy]
      simpa using congrArg Prod.fst hvs
    obtain ⟨yn,hyn⟩ := hPoint (-δ/2) (Or.inl rfl)
    obtain ⟨yp,hyp⟩ := hPoint (δ/2) (Or.inr rfl)
    have hRangeConn : IsPreconnected (Set.range F) := by
      have : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hP
      exact isPreconnected_range hF
    have hRangeSub : Set.range F ⊆ Set.Iio 0 ∪ Set.Ioi 0 := by
      rintro x ⟨y,rfl⟩
      exact lt_or_gt_of_ne (hFne y)
    have hLeft : Set.range F ⊆ Set.Iio 0 :=
      hRangeConn.subset_left_of_subset_union isOpen_Iio isOpen_Ioi
        (Set.disjoint_left.mpr (by intro x hx hy; change x < 0 at hx; change 0 < x at hy; linarith)) hRangeSub
        ⟨F yn,⟨⟨yn,rfl⟩,by change F yn < 0; rw [hyn]; linarith⟩⟩
    have hbad := hLeft ⟨yp,rfl⟩
    change F yp < 0 at hbad
    rw [hyp] at hbad
    linarith
private theorem hMarkedCrossingSigns (M : HyperellipticModel E S)
      (c d : EssentialMarkedArc M) (p : S) (hc : CrossesInDisk M c d p)
      (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) (hEp : E p = 0)
      (ρ : ℝ) (hρ : 0 < ρ) (a b : Plane)
      (haxis : ∀ x ∈ E.source, ‖E x‖ < ρ → (x ∈ c.val.image ↔ E x 1 = 0))
      (hmeet : ∀ x ∈ E.source, x ∈ c.val.image ∩ d.val.image → x = p)
      (hmodel : ∀ x ∈ E.source, ‖E x‖ < ρ → x ∈ d.val.image →
        E x ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b) : a 1 * b 1 < 0 := by
    by_contra hn
    have hprod : 0 ≤ a 1 * b 1 := le_of_not_gt hn
    have hchoice : ∃ σ : ℝ, σ ≠ 0 ∧ 0 ≤ σ*a 1 ∧ 0 ≤ σ*b 1 := by
      by_cases ha : 0 ≤ a 1
      · by_cases hb : 0 ≤ b 1
        · exact ⟨1,one_ne_zero,by simpa,by simpa⟩
        · have hblt : b 1 < 0 := lt_of_not_ge hb
          have hale : a 1 ≤ 0 := by nlinarith
          exact ⟨-1,neg_ne_zero.mpr one_ne_zero,by nlinarith,by nlinarith⟩
      · have halt : a 1 < 0 := lt_of_not_ge ha
        have hble : b 1 ≤ 0 := by nlinarith
        exact ⟨-1,neg_ne_zero.mpr one_ne_zero,by nlinarith,by nlinarith⟩
    obtain ⟨σ,hσ,ha,hb⟩ := hchoice
    apply hMarkedCrossingCannotStayInHalf M c d p hc E hpE hEp ρ σ hρ haxis
    intro x hxE hxρ hxd hxp
    have hRayNN (v : Plane) (hv : 0 ≤ σ*v 1) (hx : E x ∈ segment ℝ (0 : Plane) v) :
        0 ≤ σ*E x 1 := by
      rw [segment_eq_image'] at hx
      obtain ⟨t,ht,he⟩ := hx
      have hh := congrArg (fun z : Plane => z 1) he
      change 0 + t*(v 1-0) = E x 1 at hh
      have hmul := mul_nonneg ht.1 hv
      calc
        0 ≤ t*(σ*v 1) := hmul
        _ = σ*E x 1 := by rw [← hh]; ring
    have hxNN : 0 ≤ σ*E x 1 := (hmodel x hxE hxρ hxd).elim (hRayNN a ha) (hRayNN b hb)
    apply lt_of_le_of_ne hxNN
    intro he
    have hx0 : E x 1 = 0 := (mul_eq_zero.mp he.symm).resolve_left hσ
    have hxc : x ∈ c.val.image := (haxis x hxE hxρ).mpr hx0
    exact hxp (hmeet x hxE ⟨hxc,hxd⟩)

theorem actual_radial_core_from_interior_fan
    (M : HyperellipticModel E S) {I : Type} [Fintype I] [Nonempty I]
    (c : I → EssentialMarkedArc M) (p : S)
    (hpmark : p ∉ M.cover.branch)
    (hp : ∀ i, p ∈ (c i).val.image)
    (hfinite : ∀ i j, i ≠ j →
      (ArcSurgery.crossings M (c i) (c j)).Finite)
    (E0 : OpenPartialHomeomorph S Plane)
    (hpE : p ∈ E0.source) (hEp : E0 p = 0)
    (i0 : I) :
    ∃ τ : I → Interval, ∃ ε : ℝ, ∃ R :
      CurveComplex.FiniteStarGeometry.RadializedStar
        (fun j : I × Bool => E0 ∘ fun s : Interval =>
          (c j.1).val.map (Set.projIcc 0 1 zero_le_one
            (if j.2 then (τ j.1 : ℝ) + ε * (s : ℝ)
             else (τ j.1 : ℝ) - ε * (s : ℝ))))
        0 (E0 '' E0.source),
      R.vector (i0,true) = -R.vector (i0,false) ∧
      ∀ i x, x ∈ E0.source → ‖R.H (E0 x)‖ ≤ R.coreRadius →
        (x ∈ (c i).val.image ↔ R.H (E0 x) ∈
          segment ℝ (0:Plane) (R.vector (i,false)) ∪
          segment ℝ (0:Plane) (R.vector (i,true))) := by
  obtain ⟨τ,ε,hε,hτ,hg,hmeet,hK⟩ :=
    actual_marked_interior_contact_fan_preprocessing M c p hpmark hp hfinite
      E0.source E0.open_source hpE
  let γ : I × Bool → Interval → S := fun j s =>
    (c j.1).val.map (Set.projIcc 0 1 zero_le_one
      (if j.2 then (τ j.1 : ℝ) + ε * (s : ℝ)
       else (τ j.1 : ℝ) - ε * (s : ℝ)))
  let K : I → Set S := fun i => (c i).val.map ''
    {t : Interval | (t : ℝ) ≤ (τ i : ℝ) - ε ∨ (τ i : ℝ) + ε ≤ (t : ℝ)}
  obtain ⟨R,hop,hcore⟩ := hMarkedGermRadialCore M c p E0 hEp
    E0.source E0.open_source hpE (Subset.rfl) γ hg hmeet K hK i0
  exact ⟨τ,ε,R,hop,hcore⟩

theorem actual_normalized_chart_from_interior_fan
    (M : HyperellipticModel E S) {I : Type} [Fintype I] [Nonempty I]
    (c : I → EssentialMarkedArc M) (p : S)
    (hpmark : p ∉ M.cover.branch)
    (hp : ∀ i, p ∈ (c i).val.image)
    (hfinite : ∀ i j, i ≠ j →
      (ArcSurgery.crossings M (c i) (c j)).Finite)
    (E0 : OpenPartialHomeomorph S Plane)
    (hpE : p ∈ E0.source) (hEp : E0 p = 0)
    (i0 : I) :
    ∃ F : OpenPartialHomeomorph S Plane, ∃ ρ : ℝ,
      ∃ v w : I → Plane,
      F.source = E0.source ∧ F p = 0 ∧ 0 < ρ ∧
      (∀ x ∈ F.source, ‖F x‖ < ρ →
        (x ∈ (c i0).val.image ↔ F x 1 = 0)) ∧
      (∀ i x, x ∈ F.source → ‖F x‖ < ρ →
        (x ∈ (c i).val.image ↔ F x ∈ segment ℝ (0 : Plane) (v i) ∪
          segment ℝ (0 : Plane) (w i))) ∧
      (∀ j k : I × Bool, j ≠ k →
        Disjoint
          (segment ℝ (0 : Plane) (if j.2 then w j.1 else v j.1) \ {0})
          (segment ℝ (0 : Plane) (if k.2 then w k.1 else v k.1) \ {0})) := by
  obtain ⟨τ,ε,R,hop,hcore⟩ := actual_radial_core_from_interior_fan
    M c p hpmark hp hfinite E0 hpE hEp i0
  let γ : I × Bool → Interval → Plane := fun j => E0 ∘ fun s : Interval =>
    (c j.1).val.map (Set.projIcc 0 1 zero_le_one
      (if j.2 then (τ j.1 : ℝ) + ε * (s : ℝ)
       else (τ j.1 : ℝ) - ε * (s : ℝ)))
  obtain ⟨T,F,ρ,hsource,hzero,hρ,hρ1,hvalue,hTv,hcoreNorm,haxis,hmodel⟩ :=
    hMarkedNormalizeRadialCore M c p E0 hpE hEp γ R i0 hop false hcore
  exact ⟨F,ρ,(fun i => T (R.vector (i,false))),
    (fun i => T (R.vector (i,true))),hsource,hzero,hρ,haxis,hmodel,by
      intro j k hjk
      have hd := R.distinct_rays j k hjk
      have ht := ArcSurgery.linear_scaled_disjoint_radial_segments T 1 one_ne_zero
        (R.vector j) (R.vector k) (by simpa using hd)
      have hj : (if j.2 then T (R.vector (j.1,true)) else T (R.vector (j.1,false))) =
          T (R.vector j) := by cases j with | mk i β => cases β <;> rfl
      have hk : (if k.2 then T (R.vector (k.1,true)) else T (R.vector (k.1,false))) =
          T (R.vector k) := by cases k with | mk i β => cases β <;> rfl
      rw [hj,hk]
      simpa only [inv_one,one_smul] using ht⟩

theorem actual_unit_square_radial_chart_from_interior_fan
    (M : HyperellipticModel E S) {I : Type} [Fintype I] [Nonempty I]
    (c : I → EssentialMarkedArc M) (p : S)
    (hpmark : p ∉ M.cover.branch)
    (hp : ∀ i, p ∈ (c i).val.image)
    (hfinite : ∀ i j, i ≠ j →
      (ArcSurgery.crossings M (c i) (c j)).Finite)
    (E0 : OpenPartialHomeomorph S Plane)
    (hpE : p ∈ E0.source) (hEp : E0 p = 0)
    (i0 : I) :
    ∃ F : OpenPartialHomeomorph S Plane, ∃ v w : I → Plane,
      F.source = E0.source ∧ F p = 0 ∧
      Plane.closedSquare 0 1 ⊆ F.target ∧
      (∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
        (x ∈ (c i0).val.image ↔ F x 1 = 0)) ∧
      (∀ i x, x ∈ F.source → F x ∈ Plane.closedSquare 0 1 →
        (x ∈ (c i).val.image ↔ F x ∈ segment ℝ (0 : Plane) (v i) ∪
          segment ℝ (0 : Plane) (w i))) ∧
      (∀ j k : I × Bool, j ≠ k →
        Disjoint
          (segment ℝ (0 : Plane) (if j.2 then w j.1 else v j.1) \ {0})
          (segment ℝ (0 : Plane) (if k.2 then w k.1 else v k.1) \ {0})) := by
  obtain ⟨F₀,ρ,v₀,w₀,hsource0,hzero0,hρ,haxis0,hmodel0,hdistinct0⟩ :=
    actual_normalized_chart_from_interior_fan M c p hpmark hp hfinite
      E0 hpE hEp i0
  have hpF₀ : p ∈ F₀.source := hsource0.symm ▸ hpE
  obtain ⟨σ,F,hσ,hsource,hzero,hSquare,hvalue,hcore⟩ :=
    ArcSurgery.rescale_centered_chart_to_unit_square F₀ p hpF₀ hzero0 ρ hρ
  obtain ⟨haxis,hmodel⟩ :=
    ArcSurgery.scaled_chart_retains_radial_models F₀ F σ ρ hσ hsource
      hvalue hcore (c i0).val.image (fun i => (c i).val.image) v₀ w₀
      haxis0 hmodel0
  exact ⟨F,(fun i => σ⁻¹ • v₀ i),(fun i => σ⁻¹ • w₀ i),
    hsource.trans hsource0,hzero,hSquare,haxis,hmodel,by
      intro j k hjk
      have ht := ArcSurgery.linear_scaled_disjoint_radial_segments
        (ContinuousLinearEquiv.refl ℝ Plane) σ (ne_of_gt hσ)
        (if j.2 then w₀ j.1 else v₀ j.1)
        (if k.2 then w₀ k.1 else v₀ k.1) (hdistinct0 j k hjk)
      have hj : (if j.2 then σ⁻¹ • w₀ j.1 else σ⁻¹ • v₀ j.1) =
          σ⁻¹ • (if j.2 then w₀ j.1 else v₀ j.1) := by split_ifs <;> rfl
      have hk : (if k.2 then σ⁻¹ • w₀ k.1 else σ⁻¹ • v₀ k.1) =
          σ⁻¹ • (if k.2 then w₀ k.1 else v₀ k.1) := by split_ifs <;> rfl
      rw [hj,hk]
      simpa only [ContinuousLinearEquiv.refl_apply] using ht⟩

theorem actual_unit_square_crossing_ray_signs
    (M : HyperellipticModel E S)
    (c d : EssentialMarkedArc M) (p : S)
    (hc : ArcSurgery.CrossesInDisk M c d p)
    (F : OpenPartialHomeomorph S Plane)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (a b : Plane)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ d.val.image ↔ F x ∈ segment ℝ (0 : Plane) a ∪
        segment ℝ (0 : Plane) b))
    (hmeet : ∀ x ∈ F.source, x ∈ c.val.image ∩ d.val.image → x = p) :
    a 1 * b 1 < 0 := by
  have hsmall (x : S) (hx : ‖F x‖ < 1) :
      F x ∈ Plane.closedSquare 0 1 := by
    rw [Schoenflies.mem_closedSquare_zero_one]
    change max |F x 0| |F x 1| ≤ 1
    have h0 : |F x 0| ≤ ‖F x‖ := by
      simpa using PiLp.norm_apply_le (F x) 0
    have h1 : |F x 1| ≤ ‖F x‖ := by
      simpa using PiLp.norm_apply_le (F x) 1
    exact max_le (h0.trans hx.le) (h1.trans hx.le)
  apply hMarkedCrossingSigns M c d p hc F hpF hFp 1 (by norm_num)
    a b (fun x hx hn => haxis x hx (hsmall x hn)) hmeet
  intro x hx hn hxd
  exact (hmodel x hx (hsmall x hn)).mp hxd

theorem orient_opposite_radial_arms
    (a b : Plane) (h : a 1 * b 1 < 0) :
    ∃ v w : Plane, 0 < v 1 ∧ w 1 < 0 ∧
      (segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b =
        segment ℝ (0 : Plane) v ∪ segment ℝ (0 : Plane) w) := by
  by_cases ha : 0 < a 1
  · have hb : b 1 < 0 := by nlinarith
    exact ⟨a,b,ha,hb,rfl⟩
  · have hb : 0 < b 1 := by nlinarith
    have ha' : a 1 < 0 := by nlinarith
    exact ⟨b,a,hb,ha',Set.union_comm _ _⟩

theorem orient_radial_family
    {J : Type} (a b : J → Plane)
    (hprod : ∀ j, (a j) 1 * (b j) 1 < 0)
    (hdistinct : ∀ j k : J × Bool, j ≠ k →
      Disjoint
        (segment ℝ (0 : Plane) (if j.2 then b j.1 else a j.1) \ {0})
        (segment ℝ (0 : Plane) (if k.2 then b k.1 else a k.1) \ {0})) :
    ∃ v w : J → Plane,
      (∀ j, 0 < (v j) 1 ∧ (w j) 1 < 0) ∧
      (∀ j, segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j) =
        segment ℝ (0 : Plane) (v j) ∪ segment ℝ (0 : Plane) (w j)) ∧
      (∀ j k, j ≠ k →
        Disjoint (segment ℝ (0 : Plane) (v j) \ {0})
          (segment ℝ (0 : Plane) (v k) \ {0})) := by
  let v : J → Plane := fun j => if 0 < (a j) 1 then a j else b j
  let w : J → Plane := fun j => if 0 < (a j) 1 then b j else a j
  refine ⟨v,w,?_,?_,?_⟩
  · intro j
    dsimp [v,w]
    by_cases ha : 0 < (a j) 1
    · have hb : (b j) 1 < 0 := by nlinarith [hprod j]
      simpa [ha] using (show 0 < (a j) 1 ∧ (b j) 1 < 0 from ⟨ha,hb⟩)
    · have hb : 0 < (b j) 1 := by nlinarith [hprod j]
      have ha' : (a j) 1 < 0 := by nlinarith [hprod j]
      simpa [ha] using (show 0 < (b j) 1 ∧ (a j) 1 < 0 from ⟨hb,ha'⟩)
  · intro j
    dsimp [v,w]
    by_cases ha : 0 < (a j) 1
    · simp [ha]
    · simp [ha,Set.union_comm]
  · intro j k hjk
    dsimp [v]
    by_cases hj : 0 < (a j) 1 <;> by_cases hk : 0 < (a k) 1
    · simpa [hj,hk] using hdistinct (j,false) (k,false)
        (fun he => hjk (congrArg Prod.fst he))
    · simpa [hj,hk] using hdistinct (j,false) (k,true)
        (fun he => hjk (congrArg Prod.fst he))
    · simpa [hj,hk] using hdistinct (j,true) (k,false)
        (fun he => hjk (congrArg Prod.fst he))
    · simpa [hj,hk] using hdistinct (j,true) (k,true)
        (fun he => hjk (congrArg Prod.fst he))

theorem radial_pair_square_meet_only_center
    (M : HyperellipticModel E S) {I : Type}
    (c : I → EssentialMarkedArc M) (p : S)
    (F : OpenPartialHomeomorph S Plane)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (v w : I → Plane)
    (hmodel : ∀ i x, x ∈ F.source → F x ∈ Plane.closedSquare 0 1 →
      (x ∈ (c i).val.image ↔
        F x ∈ segment ℝ (0 : Plane) (v i) ∪
          segment ℝ (0 : Plane) (w i)))
    (hdistinct : ∀ j k : I × Bool, j ≠ k →
      Disjoint
        (segment ℝ (0 : Plane) (if j.2 then w j.1 else v j.1) \ {0})
        (segment ℝ (0 : Plane) (if k.2 then w k.1 else v k.1) \ {0}))
    (i j : I) (hij : i ≠ j) (x : S)
    (hxF : x ∈ F.source) (hxSq : F x ∈ Plane.closedSquare 0 1)
    (hxi : x ∈ (c i).val.image) (hxj : x ∈ (c j).val.image) :
    x = p := by
  have hx0 : F x = 0 := by
    by_contra hn
    have hi := (hmodel i x hxF hxSq).mp hxi
    have hj := (hmodel j x hxF hxSq).mp hxj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact Set.disjoint_left.mp (hdistinct (i,false) (j,false)
        (fun he => hij (congrArg Prod.fst he))) ⟨hi,hn⟩ ⟨hj,hn⟩
    · exact Set.disjoint_left.mp (hdistinct (i,false) (j,true)
        (fun he => hij (congrArg Prod.fst he))) ⟨hi,hn⟩ ⟨hj,hn⟩
    · exact Set.disjoint_left.mp (hdistinct (i,true) (j,false)
        (fun he => hij (congrArg Prod.fst he))) ⟨hi,hn⟩ ⟨hj,hn⟩
    · exact Set.disjoint_left.mp (hdistinct (i,true) (j,true)
        (fun he => hij (congrArg Prod.fst he))) ⟨hi,hn⟩ ⟨hj,hn⟩
  exact F.injOn hxF hpF (hx0.trans hFp.symm)

theorem actual_isolate_finite_contact_chart
    (M : HyperellipticModel E S)
    (F : OpenPartialHomeomorph S Plane) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (C : Set S) (hC : C.Finite) :
    ∃ G : OpenPartialHomeomorph S Plane,
      p ∈ G.source ∧ G p = 0 ∧ G.source ⊆ F.source ∧
      Disjoint G.source (C \ {p}) := by
  letI : T2Space S := M.sphere.symm.t2Space
  let O : Set S := F.source \ (C \ {p})
  have hO : IsOpen O := F.open_source.sdiff
    (hC.sdiff.isClosed)
  have hpO : p ∈ O := ⟨hpF,fun h => h.2 (Set.mem_singleton p)⟩
  let G := F.restrOpen O hO
  refine ⟨G,⟨hpF,hpO⟩,hFp,?_,?_⟩
  · intro x hx
    exact hx.1
  · apply Set.disjoint_left.mpr
    intro x hx hbad
    exact hx.2.2 hbad

end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.actual_radial_core_from_interior_fan
#print axioms CurveComplex.HyperellipticModel.actual_normalized_chart_from_interior_fan
#print axioms CurveComplex.HyperellipticModel.actual_unit_square_radial_chart_from_interior_fan
#print axioms CurveComplex.HyperellipticModel.actual_unit_square_crossing_ray_signs
#print axioms CurveComplex.HyperellipticModel.orient_radial_family
#print axioms CurveComplex.HyperellipticModel.actual_isolate_finite_contact_chart

#print axioms CurveComplex.HyperellipticModel.hMarkedGermRadialCore
#print axioms CurveComplex.HyperellipticModel.hMarkedNormalizeRadialCore
#print axioms CurveComplex.HyperellipticModel.hMarkedCrossingSigns
