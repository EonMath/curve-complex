import CurveComplexGenusTwo.Topology.Smoothing.JordanRegionIdentificationHeader
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Topology.LocalSurgery.LoopCircleStatement
import CurveComplexGenusTwo.Foundations.SurfaceCoverTransfer
import Mathlib.Analysis.Convex.GaugeRescale
import CurveComplexGenusTwo.Filtration.ActualFiltrationEndpointProgress
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import CurveComplexGenusTwo.Filtration.Geometry.CurveJordanBridge
import CurveComplexGenusTwo.Filtration.Geometry.ActualJordanRegionsHeader
import CurveComplexGenusTwo.Intersection.SphereChart

namespace CurveComplex.HyperellipticModel
open Set Topology
open scoped Pointwise
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Proposed bounded puncture-control conversion; intentional sorry pending review. -/
theorem actual_punctured_homotopic_jordan_sides_have_empty_region
    (M : HyperellipticModel E S) (f g : C(Interval,S)) (u v : S)
    (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hf0 : f 0 = u) (hg0 : g 0 = u) (hf1 : f 1 = v) (hg1 : g 1 = v)
    (hne : u ≠ v) (hinter : range f ∩ range g = {u,v})
    (hu : u ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
    (hv : v ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
    (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ) ⟨v,hv⟩)
    (hα : ∀ t : Interval, (α t : S) = f t)
    (hβ : ∀ t : Interval, (β t : S) = g t)
    (hhom : α.Homotopic β) :
    ∃ Ω : Set S, Ω.Nonempty ∧ IsConnected Ω ∧
      Ω ⊆ (range f ∪ range g)ᶜ ∧
      (∀ V : Set S, IsConnected V → Ω ⊆ V →
        V ⊆ (range f ∪ range g)ᶜ → V = Ω) ∧
      frontier Ω = range f ∪ range g ∧
      Disjoint Ω (M.cover.branch : Set S) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hcollision : ∀ s t : Interval, f s = g t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t h
    have hx : f s ∈ ({u,v} : Set S) := by
      rw [← hinter]
      exact ⟨mem_range_self s, ⟨t,h.symm⟩⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨hf.injective (hx.trans hf0.symm),
        hg.injective (h.symm.trans (hx.trans hg0.symm))⟩
    · exact Or.inr ⟨hf.injective (hx.trans hf1.symm),
        hg.injective (h.symm.trans (hx.trans hg1.symm))⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hf.injective hg.injective
    (hf0.trans hg0.symm) (hf1.trans hg1.symm) hcollision
  obtain ⟨J,hJ⟩ := actualCurve_sphereJordan M c
  have hmarks : ∀ x ∈ range f ∪ range g, x ∈ (M.cover.branch : Set S) → x = u := by
    intro x hx hxmark
    rcases hx with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · have ht := (α t).property
      rw [hα] at ht
      by_contra hne
      exact ht ⟨hxmark,hne⟩
    · have ht := (β t).property
      rw [hβ] at ht
      by_contra hne
      exact ht ⟨hxmark,hne⟩
  have hcard : ({u} : Finset S).card < M.cover.branch.card := by
    rw [M.cover.branch_card]
    simp
  obtain ⟨q,hqmark,hqu⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hqJ : M.sphere q ∉ J.image := by
    rw [hJ,hc]
    rintro ⟨x,hx,hxq⟩
    have heq : x = q := M.sphere.injective hxq
    subst x
    exact hqu (by simpa using hmarks q hx hqmark)
  let P : CurveComplex.SpherePort.Chart J := {
    puncture := M.sphere q
    avoids := hqJ
    plane := puncturedSpherePlane (M.sphere q) }
  obtain ⟨U,V,hU,hV,hoU,hoV,hdUV,hneUV,hcover,hfrU,hfrV⟩ := sphereJordan_two_regions J P
  have hback : M.sphere.symm '' J.image = range f ∪ range g := by
    rw [hJ,hc,← image_comp,M.sphere.symm_comp_self,image_id]
  have hcomponent : ∀ {A W : Set CurveComplex.SpherePort.Sphere},
      IsComplementComponent A W →
      IsComplementComponent (M.sphere.symm '' A) (M.sphere.symm '' W) := by
    intro A W hW
    rcases hW with ⟨hn,hconn,hsub,hmax⟩
    refine ⟨hn.image _,hconn.image _ M.sphere.symm.continuous.continuousOn,?_,?_⟩
    · rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
      exact hsub hx (M.sphere.symm.injective heq ▸ hy)
    · intro Z hZ hWZ hZA
      have hWZ' : W ⊆ M.sphere '' Z := by
        intro x hx
        exact ⟨M.sphere.symm x,hWZ ⟨x,hx,rfl⟩,M.sphere.apply_symm_apply x⟩
      have hZA' : M.sphere '' Z ⊆ Aᶜ := by
        rintro _ ⟨x,hx,rfl⟩ ha
        exact hZA hx ⟨M.sphere x,ha,M.sphere.symm_apply_apply x⟩
      have heq := hmax (M.sphere '' Z)
        (hZ.image _ M.sphere.continuous.continuousOn) hWZ' hZA'
      have himage : M.sphere.symm '' (M.sphere '' Z) = Z := by
        rw [← image_comp,M.sphere.symm_comp_self,image_id]
      rw [← himage,heq]
  have hcU := hcomponent hU
  have hcV := hcomponent hV
  rw [hback] at hcU hcV
  have hboundU : frontier (M.sphere.symm '' U) = range f ∪ range g := by
    rw [← M.sphere.symm.image_frontier,hfrU,hback]
  have hboundV : frontier (M.sphere.symm '' V) = range f ∪ range g := by
    rw [← M.sphere.symm.image_frontier,hfrV,hback]
  have hnull : (α.trans β.symm).Homotopic (Path.refl (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ)) :=
    (hhom.hcomp (Path.Homotopic.refl β.symm)).trans
      (Path.Homotopic.trans_symm β)
  have hfree : Disjoint (M.sphere.symm '' U) (M.cover.branch : Set S) ∨
      Disjoint (M.sphere.symm '' V) (M.cover.branch : Set S) := by
    by_contra hn
    rw [not_or] at hn
    obtain ⟨q₁,hq₁U,hq₁mark⟩ := Set.not_disjoint_iff.mp hn.1
    obtain ⟨q₂,hq₂V,hq₂mark⟩ := Set.not_disjoint_iff.mp hn.2
    have hq₁q₂ : q₁ ≠ q₂ := by
      intro h
      have hd : Disjoint (M.sphere.symm '' U) (M.sphere.symm '' V) :=
        (Set.disjoint_image_iff M.sphere.symm.injective).mpr hdUV
      exact Set.disjoint_left.mp hd hq₁U (h.symm ▸ hq₂V)
    have hq₁ne : q₁ ≠ u := by
      intro h
      subst q₁
      exact hcU.2.2.1 hq₁U (Or.inl ⟨0,hf0⟩)
    have hq₂ne : q₂ ≠ u := by
      intro h
      subst q₂
      exact hcV.2.2.1 hq₂V (Or.inl ⟨0,hf0⟩)
    let R : C(↑((M.cover.branch : Set S) \ {u})ᶜ, ↑({q₁,q₂} : Set S)ᶜ) := {
      toFun := fun x => ⟨x.val,by
        rintro (h | h)
        · exact x.property ⟨h.symm ▸ hq₁mark,by simpa only [mem_singleton_iff,h] using hq₁ne⟩
        · change x.val = q₂ at h
          exact x.property ⟨h.symm ▸ hq₂mark,by simpa only [mem_singleton_iff,h] using hq₂ne⟩⟩
      continuous_toFun := by fun_prop }
    have hnullTwoPunctures := hnull.map R
    have hq₂J : M.sphere q₂ ∉ J.image := by
      rw [hJ,hc]
      rintro ⟨x,hx,hxq₂⟩
      have heq : x = q₂ := M.sphere.injective hxq₂
      subst x
      exact hcV.2.2.1 hq₂V hx
    let P₂ : CurveComplex.SpherePort.Chart J := {
      puncture := M.sphere q₂
      avoids := hq₂J
      plane := puncturedSpherePlane (M.sphere q₂) }
    let C₂ := P₂.planeImage J
    have hC₂ : Schoenflies.IsJordanCurve C₂ :=
      CurveComplex.SpherePort.chart_image_jordan J P₂
    obtain ⟨e⟩ := hC₂.homeomorph_modelCurve
    obtain ⟨F,hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hC₂
      Schoenflies.isJordanCurve_modelCurve e
    have hFimage : F '' C₂ = Schoenflies.modelCurve := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        rw [hF ⟨x,hx⟩]
        exact (e ⟨x,hx⟩).property
      · intro hz
        obtain ⟨x,hx⟩ := e.surjective ⟨z,hz⟩
        refine ⟨x,x.property,?_⟩
        rw [hF x,hx]
    letI : CompactSpace S := M.sphere.symm.compactSpace
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
    let en : OpenPartialHomeomorph S Schoenflies.Plane :=
      M.sphere.toOpenPartialHomeomorph.trans (stereographic' 2 (M.sphere q₂))
    have hensource : en.source = {q₂}ᶜ := by
      ext x
      simp [en, OpenPartialHomeomorph.trans_source]
    have hentarget : en.target = Set.univ := by
      simp [en, OpenPartialHomeomorph.trans_target]
    have hU0open : IsOpen (M.sphere.symm '' U) := M.sphere.symm.isOpenMap U hoU
    have hU0closure : closure (M.sphere.symm '' U) ⊆ en.source := by
      rw [hensource, closure_eq_self_union_frontier, hboundU]
      rintro x (hx | hx) heq
      · have hd := (Set.disjoint_image_iff M.sphere.symm.injective).mpr hdUV
        exact Set.disjoint_left.mp hd hx (heq ▸ hq₂V)
      · exact hcV.2.2.1 hq₂V (heq ▸ hx)
    have hcurveSource : (range f ∪ range g) ⊆ en.source := by
      intro x hx
      exact hU0closure (frontier_subset_closure (hboundU.symm ▸ hx))
    have hC₂image : en '' (range f ∪ range g) = C₂ := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨⟨M.sphere x, ?_⟩, ?_, ?_⟩
        · intro he
          have hs := hcurveSource hx
          rw [hensource] at hs
          exact hs (M.sphere.injective he)
        · rw [hJ,hc]
          exact ⟨x,hx,rfl⟩
        · rfl
      · rintro ⟨x,hx,rfl⟩
        refine ⟨M.sphere.symm x, ?_, ?_⟩
        · rw [← hback]
          exact ⟨x,hx,rfl⟩
        · change (stereographic' 2 (M.sphere q₂)) (M.sphere (M.sphere.symm x)) = _
          rw [M.sphere.apply_symm_apply]
          rfl
    let Uplane := en '' (M.sphere.symm '' U)
    have hUplaneOpen : IsOpen Uplane := en.isOpen_image_of_subset_source hU0open
      (Set.Subset.trans subset_closure hU0closure)
    have hUplaneConn : IsConnected Uplane := hcU.2.1.image en
      (en.continuousOn.mono (Set.Subset.trans subset_closure hU0closure))
    have hUplaneBounded : Bornology.IsBounded Uplane := by
      have hk : IsCompact (closure (M.sphere.symm '' U)) := isClosed_closure.isCompact
      exact (hk.image_of_continuousOn (en.continuousOn.mono hU0closure)).isBounded.subset
        (Set.image_mono subset_closure)
    have hUisImage : en.IsImage (M.sphere.symm '' U) Uplane := by
      intro x hx
      constructor
      · rintro ⟨y,hy,he⟩
        exact en.injOn (hU0closure (subset_closure hy)) hx he ▸ hy
      · intro hy
        exact ⟨x,hy,rfl⟩
    have hUplaneFrontier : frontier Uplane = C₂ := by
      have he := hUisImage.frontier.image_eq
      have hfs : frontier (M.sphere.symm '' U) ⊆ en.source :=
        fun x hx => hU0closure (frontier_subset_closure hx)
      rw [Set.inter_eq_right.mpr hfs, hentarget, Set.univ_inter, hboundU,
        hC₂image] at he
      exact he.symm
    have hUplaneInside : Uplane = Schoenflies.inside C₂ :=
      bounded_jordan_frontier_region_eq_inside hC₂ hUplaneOpen hUplaneConn
        hUplaneBounded hUplaneFrontier
    have hq₁inside : en q₁ ∈ Schoenflies.inside C₂ := by
      rw [← hUplaneInside]
      exact ⟨q₁,hq₁U,rfl⟩
    open Schoenflies Metric in
    have hcenter : ∀ w : Schoenflies.Plane, w ∈ Schoenflies.inside Schoenflies.modelCurve →
        ∃ N : Schoenflies.Plane ≃ₜ Schoenflies.Plane, N w = 0 ∧
          N '' Schoenflies.modelCurve = Metric.sphere 0 1 := by
      intro w hw
      let A := -w +ᵥ Plane.closedSquare 0 1
      have hc : Convex ℝ A := (Plane.convex_closedSquare 0 1).vadd (-w)
      have hzero : A ∈ 𝓝 (0 : Plane) := by
        rw [← mem_interior_iff_mem_nhds]
        simpa [A, interior_vadd, mem_vadd_set_iff_neg_vadd_mem,
          Plane.interior_closedSquare, ← inside_modelCurve] using hw
      have hb : Bornology.IsBounded A := by
        have hk := Metric.isCompact_of_isClosed_isBounded (Plane.isClosed_closedSquare 0 1)
          (Plane.isBounded_closedSquare 0 1)
        exact (hk.image (Homeomorph.addLeft (-w)).continuous).isBounded
      let G := gaugeRescaleHomeomorph A (ball (0 : Plane) 1) hc hzero
        (NormedSpace.isVonNBounded_of_isBounded ℝ hb) (convex_ball 0 1)
        (ball_mem_nhds _ (by norm_num)) (NormedSpace.isVonNBounded_ball ℝ _ _)
      have hGi : G '' interior A = ball 0 1 := by
        exact (image_gaugeRescaleHomeomorph_interior ..).trans isOpen_ball.interior_eq
      have hGc : G '' closure A = closedBall 0 1 := by
        exact (image_gaugeRescaleHomeomorph_closure ..).trans (closure_ball (0 : Plane) (by norm_num))
      have hGf : G '' frontier A = Metric.sphere 0 1 := by
        rw [← closure_sdiff_interior, Set.image_sdiff G.injective, hGi, hGc]
        exact closedBall_sdiff_ball
      let N := (Homeomorph.addLeft (-w)).trans G
      refine ⟨N, ?_, ?_⟩
      · change G (-w + w) = 0
        simp [G, gaugeRescaleHomeomorph, gaugeRescaleEquiv, gaugeRescale]
      · calc
          N '' modelCurve = G '' ((Homeomorph.addLeft (-w)) '' modelCurve) :=
            (Set.image_image G (Homeomorph.addLeft (-w)) modelCurve).symm
          _ = G '' frontier A := by
            rw [modelCurve_eq_frontier, (Homeomorph.addLeft (-w)).image_frontier]
            rfl
          _ = Metric.sphere 0 1 := hGf
    have hFwinside : F (en q₁) ∈ Schoenflies.inside Schoenflies.modelCurve := by
      rw [← hFimage, ← CurveComplex.jordan_inside_homeomorph_image]
      exact ⟨en q₁,hq₁inside,rfl⟩
    obtain ⟨N,hNzero,hNimage⟩ := hcenter (F (en q₁)) hFwinside
    have hfα : Function.Injective α := by
      intro s t he
      apply hf.injective
      simpa only [hα] using congrArg Subtype.val he
    have hgβ : Function.Injective β := by
      intro s t he
      apply hg.injective
      simpa only [hβ] using congrArg Subtype.val he
    have hmeetαβ : ∀ s t, α s = β t →
        (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
      intro s t he
      apply hcollision
      simpa only [hα,hβ] using congrArg Subtype.val he
    have hloopCollision : ∀ s t, (α.trans β.symm) s = (α.trans β.symm) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
      intro s t h
      simp only [Path.trans_apply, Path.symm_apply] at h
      split_ifs at h with hs ht ht
      · left
        have he := congrArg Subtype.val (hfα h)
        apply Subtype.ext
        dsimp at he
        linarith
      · have he := hmeetαβ _ _ h
        rcases he with ⟨hs0, ht0⟩ | ⟨hs1, ht1⟩
        · right; left
          constructor <;> apply Subtype.ext
          · change (s : ℝ) = 0
            have := congrArg Subtype.val hs0; dsimp at this; linarith
          · change (t : ℝ) = 1
            have := congrArg Subtype.val ht0; simp only [unitInterval.coe_symm_eq] at this; dsimp at this; linarith
        · exfalso
          have := congrArg Subtype.val ht1
          simp only [unitInterval.coe_symm_eq] at this
          dsimp at this
          linarith
      · have he := hmeetαβ _ _ h.symm
        rcases he with ⟨ht0, hs0⟩ | ⟨ht1, hs1⟩
        · right; right
          constructor <;> apply Subtype.ext
          · change (s : ℝ) = 1
            have := congrArg Subtype.val hs0; simp only [unitInterval.coe_symm_eq] at this; dsimp at this; linarith
          · change (t : ℝ) = 0
            have := congrArg Subtype.val ht0; dsimp at this; linarith
        · exfalso
          have := congrArg Subtype.val hs1
          simp only [unitInterval.coe_symm_eq] at this
          dsimp at this
          linarith
      · left
        have he := congrArg Subtype.val (hgβ h)
        apply Subtype.ext
        simp only [unitInterval.coe_symm_eq] at he
        linarith
    obtain ⟨d,hdimage,hdnull⟩ :=
      CurveComplex.LocalSurgery.nullhomotopic_loop_with_only_endpoint_collision_gives_curve
        (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ) (α.trans β.symm) hloopCollision hnull
    have hdcarrier : Set.range (fun z => (d.map z : S)) = range f ∪ range g := by
      change Set.range (Subtype.val ∘ d.map) = _
      rw [Set.range_comp]
      change Subtype.val '' d.image = _
      rw [hdimage, Path.trans_range, Set.image_union, Path.symm_range,
        ← Set.range_comp, ← Set.range_comp]
      simp only [Function.comp_def, hα, hβ]
    let i : ℂ ≃ₗᵢ[ℝ] Schoenflies.Plane :=
      Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
    have havoid (x : ↑((M.cover.branch : Set S) \ {u})ᶜ) : x.val ≠ q₁ ∧ x.val ≠ q₂ := by
      constructor
      · intro he
        exact x.property ⟨he.symm ▸ hq₁mark, by simpa [he] using hq₁ne⟩
      · intro he
        exact x.property ⟨he.symm ▸ hq₂mark, by simpa [he] using hq₂ne⟩
    let Z : C(↑((M.cover.branch : Set S) \ {u})ᶜ, Schoenflies.Plane) := {
      toFun := fun x => M.puncturedPlane q₂ ⟨x.val,(havoid x).2⟩
      continuous_toFun := (M.puncturedPlane q₂).continuous.comp
        (continuous_subtype_val.subtype_mk _) }
    have hZeq (x : ↑((M.cover.branch : Set S) \ {u})ᶜ) : Z x = en x.val := rfl
    let T : C(↑((M.cover.branch : Set S) \ {u})ᶜ, {z : ℂ // z ≠ 0}) := {
      toFun := fun x => ⟨i.symm (N (F (Z x))),by
        intro he
        have heN : N (F (Z x)) = 0 := by
          simpa using congrArg i he
        have heF : F (Z x) = F (en q₁) := N.injective (heN.trans hNzero.symm)
        have heZ : Z x = en q₁ := F.injective heF
        have hxs : x.val ∈ en.source := by rw [hensource]; exact (havoid x).2
        have hq₁s : q₁ ∈ en.source := by rw [hensource]; exact hq₁q₂
        exact (havoid x).1 (en.injOn hxs hq₁s (by rwa [hZeq] at heZ))⟩
      continuous_toFun := by fun_prop }
    let Q : C({z : ℂ // z ≠ 0}, Circle) := {
      toFun := fun x => ⟨x.val / (‖x.val‖ : ℂ),by
        apply mem_sphere_zero_iff_norm.mpr
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
          div_self (norm_ne_zero_iff.mpr x.property)]⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.div continuous_subtype_val (by fun_prop)
        intro x
        exact_mod_cast norm_ne_zero_iff.mpr x.property }
    let L : C(Circle,Circle) := Q.comp (T.comp ⟨d.map,d.embedded.continuous⟩)
    have hLnull : L.Nullhomotopic := (hdnull.comp_right T).comp_right Q
    have hdnorm (z : Circle) : ‖(T (d.map z)).val‖ = 1 := by
      change ‖i.symm (N (F (Z (d.map z))))‖ = 1
      rw [i.symm.norm_map, hZeq]
      apply mem_sphere_zero_iff_norm.mp
      rw [← hNimage, ← hFimage, ← hC₂image]
      refine ⟨F (en (d.map z).val), ⟨en (d.map z).val, ?_, rfl⟩, rfl⟩
      refine ⟨(d.map z).val, ?_, rfl⟩
      rw [← hdcarrier]
      exact Set.mem_range_self z
    have hLval (z : Circle) : (L z : ℂ) = i.symm (N (F (en (d.map z).val))) := by
      change (T (d.map z)).val / (‖(T (d.map z)).val‖ : ℂ) = _
      rw [hdnorm]
      simp only [Complex.ofReal_one, div_one]
      rfl
    have hLinj : Function.Injective L := by
      intro z w he
      apply d.embedded.injective
      apply Subtype.ext
      apply en.injOn
        (hcurveSource (hdcarrier ▸ Set.mem_range_self z))
        (hcurveSource (hdcarrier ▸ Set.mem_range_self w))
      apply F.injective
      apply N.injective
      apply i.symm.injective
      rw [← hLval, ← hLval]
      exact congrArg Subtype.val he
    have hLsurj : Function.Surjective L := by
      intro z
      have hz : i (z : ℂ) ∈ Metric.sphere (0 : Schoenflies.Plane) 1 := by
        apply mem_sphere_zero_iff_norm.mpr
        rw [i.norm_map, Circle.norm_coe]
      have hz' : i (z : ℂ) ∈ N '' Schoenflies.modelCurve := hNimage.symm ▸ hz
      obtain ⟨p,hp,hep⟩ := hz'
      have hp' : p ∈ F '' C₂ := hFimage.symm ▸ hp
      obtain ⟨x,hx,hex⟩ := hp'
      have hx' : x ∈ en '' (range f ∪ range g) := hC₂image.symm ▸ hx
      obtain ⟨a,ha,hea⟩ := hx'
      have ha' : a ∈ Set.range (fun z => (d.map z : S)) := hdcarrier.symm ▸ ha
      obtain ⟨k,hek⟩ := ha'
      dsimp only at hek
      refine ⟨k,Subtype.ext ?_⟩
      rw [hLval,hek,hea,hex,hep,i.symm_apply_apply]
    let H : Circle ≃ₜ Circle :=
      (L.continuous.isClosedEmbedding hLinj).isEmbedding.toHomeomorphOfSurjective hLsurj
    have hnId : (ContinuousMap.id Circle).Nullhomotopic := by
      have hh := hLnull.comp_left (⟨H.symm,H.symm.continuous⟩ : C(Circle,Circle))
      have heq : L.comp (⟨H.symm,H.symm.continuous⟩ : C(Circle,Circle)) =
          ContinuousMap.id Circle := by
        apply ContinuousMap.ext
        intro z
        exact H.apply_symm_apply z
      rw [heq] at hh
      exact hh
    have hcircle : ¬ (ContinuousMap.id Circle).Nullhomotopic := by
      intro hn
      obtain ⟨g,hg⟩ := CurveComplex.exists_lift_of_nullhomotopic Circle.exp
        Circle.isCoveringMap_exp (ContinuousMap.id Circle) hn Circle.exp_surjective
      have hgexp (z : Circle) : Circle.exp (g z) = z := by
        exact congrArg (fun f : C(Circle,Circle) => f z) hg
      have hsame : (fun t : ℝ => g (Circle.exp t)) = (fun t => t + g 1) := by
        apply Circle.isCoveringMap_exp.eq_of_comp_eq
          (g.continuous.comp Circle.exp.continuous) (by fun_prop) (by
            funext t
            simp only [Function.comp_apply, hgexp, Circle.exp_add, hgexp 1, mul_one]) 0
        simp
      have he := congrFun hsame (2 * Real.pi)
      simp only [Circle.exp_two_pi] at he
      have hp := Real.pi_pos
      linarith
    exact hcircle hnId
  rcases hfree with hfree | hfree
  · exact ⟨M.sphere.symm '' U,hcU.1,hcU.2.1,hcU.2.2.1,hcU.2.2.2,hboundU,hfree⟩
  · exact ⟨M.sphere.symm '' V,hcV.1,hcV.2.1,hcV.2.2.1,hcV.2.2.2,hboundV,hfree⟩

end CurveComplex.HyperellipticModel
