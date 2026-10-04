import CurveComplexGenusTwo.Topology.Smoothing.ActualSmoothChartStar
import CurveComplexGenusTwo.Topology.Smoothing.ActualStarIntersection
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import CurveComplexGenusTwo.Topology.Smoothing.EndpointCoordinateDisks
import CurveComplexGenusTwo.Topology.Smoothing.GermsInsideCoordinateDisks
import CurveComplexGenusTwo.Topology.Smoothing.FiniteActualStarRadialization
import CurveComplexGenusTwo.Topology.ChartLift
open Set Metric Schoenflies CurveComplex.FiniteStarGeometry
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1200000

theorem actual_endpoint_star_normalization
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    (ι : Type) [Fintype ι] (a : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (a i)) (arcInterior M (a j)))
    (p : S) (hp : p ∈ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    letI := C.charts
    ∃ (H : AmbientIsotopy S) (r : ℝ) (hr : 0 < r) (hrhalf : r < 1 / 2)
      (v : ι × Bool → EuclideanSpace ℝ (Fin 2)),
      (∀ t b, b ∈ M.cover.branch → H.map (t, b) = b) ∧
      (∀ t x, x ∉ W → H.map (t, x) = x) ∧
      ∀ (i : ι) (terminal : Bool),
        (if terminal then (a i).val.map ⟨1, by norm_num⟩
          else (a i).val.map ⟨0, by norm_num⟩) = p →
        v (i, terminal) ≠ 0 ∧
        (segment ℝ ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p)
          ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p + v (i, terminal)) ⊆
          (chartAt (EuclideanSpace ℝ (Fin 2)) p).target) ∧
        H.finalMap '' Set.range ((a i).val.map ∘
          endpointGermParameter terminal r hr (by linarith)) =
          (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ''
            segment ℝ ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p)
              ((chartAt (EuclideanSpace ℝ (Fin 2)) p) p + v (i, terminal)) := by
  classical
  letI := C.charts
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  have pointedIsotopy (o : Plane) (R : ℝ) (hR : 0 < R) (F : Plane ≃ₜ Plane)
      (hFo : F o = o) (hfix : ∀ x, x ∉ ball o R → F x = x) :
      ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
        (∀ t, H.map (t,o) = o) ∧ ∀ t x, x ∉ ball o R → H.map (t,x) = x := by
    have zero (R : ℝ) (hR : 0 < R) (F : Plane ≃ₜ Plane)
        (hFfix : ∀ x, R ≤ ‖x‖ → F x = x) (hFzero : F 0 = 0) :
        ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
          (∀ t x, R ≤ ‖x‖ → H.map (t,x) = x) ∧ ∀ t, H.map (t,0) = 0 := by
      have hFbound (x : Plane) (hx : ‖x‖ ≤ R) : ‖F x‖ ≤ R := by
        by_contra hn
        have heq : F x = x := F.injective (hFfix (F x) (le_of_not_ge hn))
        exact hn (by rw [heq]; exact hx)
      have hdisp (x : Plane) : ‖F x - x‖ ≤ 2 * R := by
        by_cases hx : ‖x‖ ≤ R
        · exact (norm_sub_le _ _).trans (by linarith [hFbound x hx])
        · rw [hFfix x (le_of_not_ge hx), sub_self, norm_zero]
          linarith
      let G : Interval × Plane → Plane := fun z =>
        if (z.1 : ℝ) = 0 then z.2 else (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2)
      have hGbound (z : Interval × Plane) :
          dist (G z) z.2 ≤ (2 * R) * (z.1 : ℝ) := by
        by_cases ht : (z.1 : ℝ) = 0
        · simp only [G, ht, ite_true, dist_self, mul_zero, le_refl]
        · dsimp only [G]
          rw [if_neg ht, dist_eq_norm]
          have heq : (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2) - z.2 =
              (z.1 : ℝ) • (F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2) := by
            rw [smul_sub, smul_smul, mul_inv_cancel₀ ht, one_smul]
          rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg z.1.property.1]
          calc
            (z.1 : ℝ) * ‖F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2‖ ≤
                (z.1 : ℝ) * (2 * R) :=
              mul_le_mul_of_nonneg_left (hdisp _) z.1.property.1
            _ = (2 * R) * (z.1 : ℝ) := mul_comm _ _
      have hGc : Continuous G := by
        rw [continuous_iff_continuousAt]
        intro z
        by_cases ht : (z.1 : ℝ) = 0
        · have hGz : G z = z.2 := by simp only [G, ht, ite_true]
          change Filter.Tendsto G (nhds z) (nhds (G z))
          rw [hGz, tendsto_iff_dist_tendsto_zero]
          have hlim : Filter.Tendsto
              (fun w : Interval × Plane => (2 * R) * (w.1 : ℝ) + dist w.2 z.2)
              (nhds z) (nhds 0) := by
            have hc : Continuous (fun w : Interval × Plane =>
                (2 * R) * (w.1 : ℝ) + dist w.2 z.2) := by fun_prop
            simpa only [ContinuousAt, ht, mul_zero, dist_self, add_zero] using hc.continuousAt (x := z)
          exact squeeze_zero (fun w => dist_nonneg) (fun w =>
            (dist_triangle (G w) w.2 z.2).trans (add_le_add (hGbound w) le_rfl)) hlim
        · have hc : ContinuousAt
              (fun w : Interval × Plane => (w.1 : ℝ) • F ((w.1 : ℝ)⁻¹ • w.2)) z := by
            fun_prop (disch := assumption)
          apply hc.congr_of_eventuallyEq
          have hevent : ∀ᶠ w : Interval × Plane in nhds z, (w.1 : ℝ) ≠ 0 :=
            (continuous_subtype_val.comp continuous_fst).continuousAt.eventually_ne ht
          exact hevent.mono (fun w hw => if_neg hw)
      refine ⟨{ map := ⟨G, hGc⟩, homeomorphism_at := ?_, at_zero := ?_ }, ?_, ?_, ?_⟩
      · intro t
        by_cases ht : (t : ℝ) = 0
        · exact ⟨Homeomorph.refl _, fun x => by
            change x = G (t, x)
            simp only [G, ht, ite_true]⟩
        · let u : ℝˣ := Units.mk0 (t : ℝ) ht
          let e := ((Homeomorph.smul u⁻¹).trans F).trans (Homeomorph.smul u)
          refine ⟨e, ?_⟩
          intro x
          change (t : ℝ) • F ((t : ℝ)⁻¹ • x) = G (t, x)
          dsimp only [G]
          rw [if_neg ht]
      · intro x
        simp [G]
      · funext x
        simp [AmbientIsotopy.finalMap, G]
      · intro t x hx
        change G (t, x) = x
        by_cases ht : (t : ℝ) = 0
        · simp only [G, ht, ite_true]
        · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
          have hlarge : R ≤ ‖(t : ℝ)⁻¹ • x‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), inv_mul_eq_div]
            apply (le_div_iff₀ htpos).mpr
            nlinarith [t.property.2]
          simp only [G, if_neg ht, hFfix _ hlarge, smul_smul, mul_inv_cancel₀ ht, one_smul]
      · intro t
        change G (t,0) = 0
        by_cases ht : (t:ℝ) = 0
        · simp only [G,ht,ite_true]
        · simp only [G,if_neg ht,smul_zero,hFzero]
    have conjugate {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
        (e : X ≃ₜ Y) (H : AmbientIsotopy Y) :
        ∃ K : AmbientIsotopy X, ∀ t x, K.map (t,x) = e.symm (H.map (t,e x)) := by
      refine ⟨{ map := ⟨fun z => e.symm (H.map (z.1,e z.2)),
        e.symm.continuous.comp (H.map.continuous.comp
          (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩,
                homeomorphism_at := ?_, at_zero := ?_ },fun _ _ => rfl⟩
      · intro t
        obtain ⟨h,hh⟩ := H.homeomorphism_at t
        exact ⟨(e.trans h).trans e.symm,fun x => congrArg e.symm (hh (e x))⟩
      · intro x
        change e.symm (H.map (⟨0,by norm_num⟩,e x)) = x
        rw [H.at_zero,e.symm_apply_apply]
    let E : Plane ≃ₜ Plane := Homeomorph.addLeft (-o)
    have hEo : E o = 0 := by simp [E]
    have hEinv : E.symm 0 = o := by
      apply E.injective
      rw [E.apply_symm_apply,hEo]
    have hdist : ∀ x, dist (E x) 0 = dist x o := by
      intro x
      simp [E,dist_eq_norm,sub_eq_add_neg,add_comm]
    let A : Plane ≃ₜ Plane := (E.symm.trans F).trans E
    have hA0 : A 0 = 0 := by
      change E (F (E.symm 0)) = 0
      rw [hEinv,hFo,hEo]
    have hAfix : ∀ x, R ≤ ‖x‖ → A x = x := by
      intro x hx
      have hxout : E.symm x ∉ ball o R := by
        have hh := hdist (E.symm x)
        rw [E.apply_symm_apply,dist_zero_right] at hh
        simp only [mem_ball]
        exact not_lt.mpr (hh ▸ hx)
      change E (F (E.symm x)) = x
      rw [hfix _ hxout,E.apply_symm_apply]
    obtain ⟨H,hHF,hHfix,hH0⟩ := zero R hR A hAfix hA0
    obtain ⟨K,hK⟩ := conjugate E H
    refine ⟨K,?_,?_,?_⟩
    · funext x
      change K.map (⟨1,by norm_num⟩,x) = F x
      rw [hK]
      change E.symm (H.finalMap (E x)) = F x
      rw [hHF]
      change E.symm (E (F (E.symm (E x)))) = F x
      rw [E.symm_apply_apply,E.symm_apply_apply]
    · intro t
      rw [hK,hEo,hH0,hEinv]
    · intro t x hx
      rw [hK]
      have hxnorm : R ≤ ‖E x‖ := by
        have hh := hdist x
        rw [dist_zero_right] at hh
        exact not_lt.mp (by simpa only [mem_ball,← hh] using hx)
      rw [hHfix t _ hxnorm,E.symm_apply_apply]
  have nested (γ : I → Plane) (hγ : Topology.IsClosedEmbedding γ)
      (o : Plane) (hstart : γ zeroI = o) (H : Plane ≃ₜ Plane) (hH : H o = o)
      (c d : I) (hd : 0 < d.val) (hdc : d.val ≤ c.val) (v : Plane) (hv : v ≠ 0)
      (hrad : H '' armPrefix (fun _ : Unit => γ) () c = segment ℝ o (o+v)) :
      H '' armPrefix (fun _ : Unit => γ) () d = segment ℝ o (H (γ d)) ∧ H (γ d) ≠ o := by
    let k : I → I := fun t => ⟨d.val*t.val,by
      constructor
      · exact mul_nonneg d.property.1 t.property.1
      · nlinarith [d.property.1,d.property.2,t.property.1,t.property.2]⟩
    let η : Path o (H (γ d)) := {
      toFun := H ∘ γ ∘ k
      continuous_toFun := H.continuous.comp (hγ.continuous.comp (by fun_prop))
      source' := by simpa [k] using (congrArg H hstart).trans hH
      target' := by simp [k] }
    have hη : Function.Injective η := by
      intro t u he
      have hh := congrArg Subtype.val (hγ.injective (H.injective he))
      change d.val*t.val = d.val*u.val at hh
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hd) hh)
    have himage : range η = H '' armPrefix (fun _ : Unit => γ) () d := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨γ (k t),⟨k t,by change d.val*t.val ≤ d.val; nlinarith [d.property.1,t.property.2],rfl⟩,rfl⟩
      · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩
        let u : I := ⟨t.val/d.val,⟨div_nonneg t.property.1 hd.le,(div_le_one hd).mpr ht⟩⟩
        refine ⟨u,?_⟩
        change H (γ (k u)) = H (γ t)
        congr 2
        apply Subtype.ext
        change d.val*(t.val/d.val) = t.val
        field_simp
    have hA : IsArcBetween (range η) o (H (γ d)) := by
      refine ⟨η.extend,η.continuous_extend.continuousOn,?_,?_,η.extend_zero,η.extend_one⟩
      · intro s hs t ht he
        rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
        exact congrArg Subtype.val (hη he)
      · exact η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))
    have hneq : H (γ d) ≠ o := by
      intro he
      have hdz : d = zeroI := hγ.injective ((H.injective (he.trans hH.symm)).trans hstart.symm)
      have hh : d.val = 0 := congrArg Subtype.val hdz
      linarith
    have hvend : o ≠ o+v := by
      intro he
      apply hv
      have hh := congrArg (fun x => x-o) he
      simpa only [sub_self,add_sub_cancel_left] using hh.symm
    have hC := isArcBetween_segment hvend
    have hAC : range η ⊆ segment ℝ o (o+v) := by
      rw [himage,← hrad]
      apply image_mono
      apply image_mono
      intro t ht
      exact ht.trans hdc
    have hqC : H (γ d) ∈ segment ℝ o (o+v) := by
      rw [← hrad]
      exact ⟨γ d,⟨d,hdc,rfl⟩,rfl⟩
    have hBC : segment ℝ o (H (γ d)) ⊆ segment ℝ o (o+v) :=
      (convex_segment o (o+v)).segment_subset (left_mem_segment ℝ o (o+v)) hqC
    exact ⟨himage.symm.trans (hA.eq_of_subset_arc (isArcBetween_segment hneq.symm) hC hAC hBC),hneq⟩
  obtain ⟨U,hU,hpU,hUchart,hmarks,hcentral,hnoninc,rOld,hrOld,hrOldHalf,hOldGerms⟩ :=
    actual_endpoint_star_in_smooth_chart M C ι a p hp
  let D := U ∩ W
  have hD : IsOpen D := hU.inter hW
  have hpD : p ∈ D := ⟨hpU,hpW⟩
  let e := chartAt Plane p
  have hDchart : D ⊆ e.source := fun x hx => hUchart hx.1
  obtain ⟨R,hR,htarget,hdiskD,hcompact⟩ := coordinate_disk_inside p D hD hpD hDchart
  obtain ⟨r₀,hr₀,hr₀half,hstarts,hends⟩ := uniform_actual_endpoint_germs M ι a p D hD hpD
  have hr₀1 : r₀ < 1 := by linarith
  let α : ι × Bool → Interval → S := fun x =>
    (a x.1).val.map ∘ endpointGermParameter x.2 r₀ hr₀ hr₀1
  let J := {x : ι × Bool // α x CurveComplex.FiniteStarGeometry.zeroI = p}
  let γ : J → Interval → Plane := fun j => e ∘ α j.val
  have hsource : ∀ (j : J) (t : Interval), α j.val t ∈ e.source := by
    intro j t
    apply hDchart
    cases hb : j.val.2
    · have hpj : (a j.val.1).val.map ⟨0,by norm_num⟩ = p := by
        simpa [α,endpointGermParameter,hb,CurveComplex.FiniteStarGeometry.zeroI] using j.property
      apply hstarts j.val.1 hpj
      rw [hb]
      change r₀*t.val ≤ r₀
      nlinarith [t.property.2]
    · have hpj : (a j.val.1).val.map ⟨1,by norm_num⟩ = p := by
        simpa [α,endpointGermParameter,hb,CurveComplex.FiniteStarGeometry.zeroI] using j.property
      apply hends j.val.1 hpj
      rw [hb]
      change 1-r₀ ≤ 1-r₀*t.val
      nlinarith [t.property.2]
  have hγ : ∀ j : J, Topology.IsClosedEmbedding (γ j) := by
    intro j
    have hα := actual_endpoint_germ_embedding M (a j.val.1) j.val.2 r₀ hr₀ hr₀1
    have hc : Continuous (γ j) := continuousOn_univ.mp
      (e.continuousOn.comp hα.continuous.continuousOn (fun t _ => hsource j t))
    apply hc.isClosedEmbedding
    intro s t he
    exact hα.injective (e.injOn (hsource j s) (hsource j t) he)
  have hstart : ∀ j : J, γ j CurveComplex.FiniteStarGeometry.zeroI = e p := by
    intro j
    change e (α j.val CurveComplex.FiniteStarGeometry.zeroI) = e p
    rw [j.property]
  have hmeet : ∀ i j : J, i ≠ j → range (γ i) ∩ range (γ j) = {e p} := by
    intro i j hij
    have hij' : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    have hreal := actual_normalized_star_intersection M a hd p r₀ hr₀ hr₀half
      i.val j.val hij' (by simpa [α,CurveComplex.FiniteStarGeometry.zeroI] using i.property)
      (by simpa [α,CurveComplex.FiniteStarGeometry.zeroI] using j.property)
    ext x
    constructor
    · rintro ⟨⟨s,hs⟩,⟨t,ht⟩⟩
      have he : α i.val s = α j.val t := e.injOn (hsource i s) (hsource j t) (hs.trans ht.symm)
      have hz : α i.val s = p := by
        have hh : α i.val s ∈ range (α i.val) ∩ range (α j.val) := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
        rw [hreal] at hh
        exact hh
      exact mem_singleton_iff.mpr (hs.symm.trans (congrArg e hz))
    · intro hx
      have hx' : x = e p := hx
      subst x
      exact ⟨⟨CurveComplex.FiniteStarGeometry.zeroI,hstart i⟩,
        ⟨CurveComplex.FiniteStarGeometry.zeroI,hstart j⟩⟩
  obtain ⟨star⟩ := CurveComplex.FiniteStarGeometry.finite_actual_star_radialization γ (e p)
    hγ hstart hmeet (ball (e p) R) isOpen_ball (by simpa using hR)
  have hsupportTarget : closedBall (e p) star.supportRadius ⊆ e.target := by
    intro z hz
    exact htarget (ball_subset_closedBall (star.support_subset hz))
  obtain ⟨P,hPfinal,hPcenter,hPoutside⟩ := pointedIsotopy (e p) star.supportRadius star.support_pos
    star.H star.fixes_center star.fixes_exterior
  have hPclosed : ∀ t z, z ∉ closedBall (e p) star.supportRadius → P.map (t,z) = z := by
    intro t z hz
    exact hPoutside t z (fun hh => hz (ball_subset_closedBall hh))
  obtain ⟨K,G,hcoord,hGU,hGoutside⟩ := position_surface_chart_lift S e.source e.target
    e.open_source e.toHomeomorphSourceTarget (closedBall (e p) star.supportRadius)
    (isCompact_closedBall _ _) hsupportTarget P hPclosed
  have hcoord' (t : Interval) (x : e.source) :
      e (K.map (t,x)) = P.map (t,e x) := by
    simpa only [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe] using hcoord t x
  have hGpoint (t : Interval) (x : S) (hx : x ∈ e.source) :
      G.map (t,x) = e.symm (P.map (t,e x)) := by
    rw [hGU t ⟨x,hx⟩,← hcoord' t ⟨x,hx⟩]
    exact (e.left_inv (K.map (t,⟨x,hx⟩)).property).symm
  have hGoutD : ∀ t x, x ∉ D → G.map (t,x) = x := by
    intro t x hxD
    by_cases hx : x ∈ e.source
    · have hzout : e x ∉ closedBall (e p) star.supportRadius := by
        intro hz
        have hzin : e x ∈ closedBall (e p) R := ball_subset_closedBall (star.support_subset hz)
        have hxD' : e.symm (e x) ∈ D := hdiskD ⟨e x,hzin,rfl⟩
        rw [e.left_inv hx] at hxD'
        exact hxD hxD'
      rw [hGpoint t x hx,hPclosed t (e x) hzout,e.left_inv hx]
    · exact hGoutside t x hx
  have hGcenter : ∀ t, G.map (t,p) = p := by
    intro t
    rw [hGpoint t p (mem_chart_source Plane p),hPcenter,e.left_inv (mem_chart_source Plane p)]
  have hGmarks : ∀ t b, b ∈ M.cover.branch → G.map (t,b) = b := by
    intro t b hb
    by_cases hbp : b = p
    · subst b; exact hGcenter t
    · apply hGoutD
      intro hbD
      exact hbp (hmarks b hb hbD.1)
  have small (s : Finset J) : ∃ d : ℝ, 0 < d ∧ d < 1 ∧ ∀ j ∈ s, d < (star.cut j).val := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1/2,by norm_num,by norm_num,by simp⟩
    | @insert j s hj ih =>
      obtain ⟨d,hd,hd1,hds⟩ := ih
      refine ⟨min d ((star.cut j).val/2),lt_min hd (half_pos (star.cut_pos j)),
        (min_le_left _ _).trans_lt hd1,?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with he|hi
      · subst i
        exact (min_le_right _ _).trans_lt (by linarith [star.cut_pos j])
      · exact (min_le_left _ _).trans_lt (hds i hi)
  obtain ⟨d,hd,hd1,hds⟩ := small Finset.univ
  let q : Interval := ⟨d,⟨hd.le,hd1.le⟩⟩
  let r := r₀*d
  have hr : 0 < r := mul_pos hr₀ hd
  have hrhalf : r < 1/2 := by
    have hh : r₀*d < r₀ := by nlinarith
    exact hh.trans hr₀half
  let v : ι × Bool → Plane := fun x =>
    if hx : α x CurveComplex.FiniteStarGeometry.zeroI = p then
      star.H (γ ⟨x,hx⟩ q) - e p else 0
  have hTargetPreserved : ∀ z ∈ e.target, star.H z ∈ e.target := by
    intro z hz
    by_contra hn
    have hout : star.H z ∉ ball (e p) star.supportRadius := by
      intro hh
      exact hn (hsupportTarget (ball_subset_closedBall hh))
    have he : star.H z = z := star.H.injective (star.fixes_exterior _ hout)
    exact hn (he.symm ▸ hz)
  refine ⟨G,r,hr,hrhalf,v,hGmarks,?_,?_⟩
  · intro t x hx
    exact hGoutD t x (fun hh => hx hh.2)
  · intro i terminal hi
    have hx : α (i,terminal) CurveComplex.FiniteStarGeometry.zeroI = p := by
      cases terminal <;> simpa [α,endpointGermParameter,CurveComplex.FiniteStarGeometry.zeroI] using hi
    let j : J := ⟨(i,terminal),hx⟩
    have hv : v (i,terminal) = star.H (γ j q) - e p := by simp only [v,dif_pos hx]; rfl
    have hend : e p + v (i,terminal) = star.H (γ j q) := by rw [hv]; abel
    obtain ⟨hsmall,hne⟩ := nested (γ j) (hγ j) (e p) (hstart j) star.H star.fixes_center
      (star.cut j) q hd (hds j (Finset.mem_univ j)).le (star.vector j) (star.vector_nonzero j)
      (by simpa only [CurveComplex.FiniteStarGeometry.armPrefix] using star.prefix_image j)
    refine ⟨by rw [hv]; exact sub_ne_zero.mpr hne,?_,?_⟩
    · rw [hend,← hsmall]
      rintro z ⟨_,⟨t,ht,rfl⟩,rfl⟩
      exact hTargetPreserved _ (e.map_source (hsource j t))
    · let k : Interval → Interval := fun t => ⟨d*t.val,by
        constructor
        · exact mul_nonneg hd.le t.property.1
        · nlinarith [t.property.2]⟩
      have hkRange : range k = {t : Interval | t.val ≤ d} := by
        ext t
        constructor
        · rintro ⟨u,rfl⟩
          change d*u.val ≤ d
          nlinarith [u.property.2]
        · intro ht
          let u : Interval := ⟨t.val/d,⟨div_nonneg t.property.1 hd.le,(div_le_one hd).mpr ht⟩⟩
          refine ⟨u,?_⟩
          apply Subtype.ext
          change d*(t.val/d) = t.val
          field_simp
      have hparam : (a i).val.map ∘ endpointGermParameter terminal r hr (by linarith) = α j.val ∘ k := by
        funext t
        change (a i).val.map _ = (a i).val.map _
        congr 1
        apply Subtype.ext
        cases terminal <;> dsimp [endpointGermParameter,α,k,r,j] <;> ring
      rw [hparam,range_comp,hkRange,hend]
      have hEq : EqOn G.finalMap (e.symm ∘ star.H ∘ e) (α j.val '' {t : Interval | t.val ≤ d}) := by
        rintro x ⟨t,ht,rfl⟩
        change G.map (⟨1,by norm_num⟩,α j.val t) = _
        rw [hGpoint _ _ (hsource j t)]
        change e.symm (P.finalMap (γ j t)) = e.symm (star.H (γ j t))
        rw [hPfinal]
      rw [hEq.image_eq,image_comp,image_comp]
      have hγimage : e '' (α j.val '' {t : Interval | t.val ≤ d}) =
          CurveComplex.FiniteStarGeometry.armPrefix (fun _ : Unit => γ j) () q := by
        exact (image_comp e (α j.val) {t : Interval | t.val ≤ d}).symm
      rw [hγimage,hsmall]

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_endpoint_star_normalization
