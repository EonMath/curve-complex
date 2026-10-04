import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Foundations.PlanarDiscRecognition
import CurveComplexGenusTwo.Dictionary.JordanDiscHelper
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import ClassificationOfSurfaces.Moise.Brouwer
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1600000
theorem one_branch_disc_boundary_sheet_exchange (M : HyperellipticModel E S) (f : C(Metric.closedBall (0 : Schoenflies.Plane) 1, S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0 : Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z = m)
    (β : C(Interval, Metric.closedBall (0 : Schoenflies.Plane) 1))
    (hends : β 0 = β 1)
    (hcoll : ∀ s t, β s = β t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
    (hrange : Set.range β = {z | ‖z.val‖ = 1})
    (γ : C(Interval, E)) (hγπ : ∀ t, M.cover.projection (γ t) = f (β t)) :
    γ 1 = M.cover.deck (γ 0) := by
  have hsmallFiber (w : E) (hw : M.cover.projection w ∈ M.cover.branch)
    (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall (0 : ℂ) r ⊆ (M.cover.branch_chart w hw).upstairs.target)
    (b : S) (hb : b ∈ (M.cover.branch_chart w hw).downstairs.source)
    (hbnorm : ‖(M.cover.branch_chart w hw).downstairs b‖ ≤ r^2)
    (hbzero : (M.cover.branch_chart w hw).downstairs b ≠ 0) :
    b ∉ M.cover.branch ∧
      ∀ x, M.cover.projection x = b → x ∈ (M.cover.branch_chart w hw).upstairs.source := by
    let c := M.cover.branch_chart w hw
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c.downstairs b) (by norm_num : 0 < 2)
    have hzNorm : ‖z‖ ≤ r := by
      have he : ‖z‖^2 = ‖c.downstairs b‖ := by rw [← norm_pow, hz]
      nlinarith [norm_nonneg z]
    have hzmem : z ∈ c.upstairs.target := hball (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hzNorm)
    have hnzmem : -z ∈ c.upstairs.target := hball (by
      simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hzNorm)
    let y := c.upstairs.symm z
    let y' := c.upstairs.symm (-z)
    have hysrc : y ∈ c.upstairs.source := c.upstairs.map_target hzmem
    have hy'src : y' ∈ c.upstairs.source := c.upstairs.map_target hnzmem
    have hycoord : c.upstairs y = z := c.upstairs.right_inv hzmem
    have hy'coord : c.upstairs y' = -z := c.upstairs.right_inv hnzmem
    have hyπ : M.cover.projection y = b := by
      apply c.downstairs.injOn (c.image_mem _ hysrc) hb
      rw [c.square _ hysrc, hycoord, hz]
    have hy'π : M.cover.projection y' = b := by
      apply c.downstairs.injOn (c.image_mem _ hy'src) hb
      rw [c.square _ hy'src, hy'coord, neg_sq, hz]
    have hyne : y ≠ y' := by
      intro he
      have hzz : z = -z := by
        calc z = c.upstairs y := hycoord.symm
             _ = c.upstairs y' := congrArg c.upstairs he
             _ = -z := hy'coord
      have hz0 := CharZero.eq_neg_self_iff.mp hzz
      exact hbzero (hz.symm.trans (by rw [hz0]; norm_num))
    have hydeck : y' = M.cover.deck y := by
      rcases (M.cover.fiber_pair y y').mp (hyπ.trans hy'π.symm) with he | he
      · exact False.elim (hyne he.symm)
      · exact he
    have hbnot : b ∉ M.cover.branch := by
      intro hbranch
      have hyfix := (M.cover.fixed_iff_branch y).mpr (hyπ ▸ hbranch)
      exact hyne (hydeck.trans hyfix).symm
    refine ⟨hbnot, ?_⟩
    intro x hx
    rcases (M.cover.fiber_pair y x).mp (hyπ.trans hx.symm) with he | he
    · simpa only [he] using hysrc
    · simpa only [he, ← hydeck] using hy'src
  have hfreeLoop (H : C(Interval × Interval, S))
    (hloop : ∀ s, H (s, 0) = H (s, 1))
    (havoid : ∀ z, H z ∉ M.cover.branch)
    (γ : C(Interval, E)) (hγπ : ∀ t, M.cover.projection (γ t) = H (1, t))
    (hγends : γ 0 = γ 1) :
    ∃ δ : C(Interval, E), (∀ t, M.cover.projection (δ t) = H (0, t)) ∧ δ 0 = δ 1 := by
    let : ContractibleSpace Interval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
    let : LocallyPathConnectedSpace Interval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
    obtain ⟨Γ, hΓ, _⟩ := M.cover.unbranched_cover.existsUnique_continuousMap_lifts
      H (hγπ 0) havoid
    have hΓπ (z) : M.cover.projection (Γ z) = H z := congrFun hΓ.2 z
    let γ' : C(Interval, E) := ⟨fun t => Γ (1,t),
      Γ.continuous.comp (continuous_const.prodMk continuous_id)⟩
    let β : C(Interval, S) := ⟨fun t => H (1,t),
      H.continuous.comp (continuous_const.prodMk continuous_id)⟩
    obtain ⟨f, hf, hu⟩ := M.cover.unbranched_cover.existsUnique_continuousMap_lifts
      β (hγπ 0) (fun t => havoid (1,t))
    have hγf : γ = f := hu γ ⟨rfl, funext hγπ⟩
    have hγ'f : γ' = f := hu γ' ⟨hΓ.1, funext (fun t => hΓπ (1,t))⟩
    have hΓend : Γ (1,0) = Γ (1,1) := by
      exact (congrFun (congrArg DFunLike.coe (hγ'f.trans hγf.symm)) 0).trans
        (hγends.trans (congrFun (congrArg DFunLike.coe (hγf.trans hγ'f.symm)) 1))
    have hUavoid (s : Interval) : Γ (s,0) ∉ M.cover.ramification := by
      change M.cover.projection (Γ (s,0)) ∉ M.cover.branch
      rw [hΓπ]; exact havoid _
    have hVavoid (s : Interval) : Γ (s,1) ∉ M.cover.ramification := by
      change M.cover.projection (Γ (s,1)) ∉ M.cover.branch
      rw [hΓπ]; exact havoid _
    let u : C(Interval, M.cover.unramifiedTotal) :=
      ⟨fun s => ⟨Γ (s,0), hUavoid s⟩,
        (Γ.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk hUavoid⟩
    let v : C(Interval, M.cover.unramifiedTotal) :=
      ⟨fun s => ⟨Γ (s,1), hVavoid s⟩,
        (Γ.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk hVavoid⟩
    have huv : M.cover.unramifiedProjection ∘ u = M.cover.unramifiedProjection ∘ v := by
      funext s
      apply Subtype.ext
      exact (hΓπ (s,0)).trans ((hloop s).trans (hΓπ (s,1)).symm)
    have heq : u = v := by
      apply DFunLike.coe_injective
      exact M.cover.unramified_isCoveringMap.eq_of_comp_eq u.continuous v.continuous huv
        1 (Subtype.ext hΓend)
    let δ : C(Interval, E) := ⟨fun t => Γ (0,t),
      Γ.continuous.comp (continuous_const.prodMk continuous_id)⟩
    refine ⟨δ, fun t => hΓπ (0,t), ?_⟩
    exact congrArg (fun f : C(Interval, M.cover.unramifiedTotal) => (f (0 : Interval)).val) heq
  have hsquare (β γ : C(Interval, ℂ))
    (hcoll : ∀ s t, β s = β t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
    (hroot : ∀ t, γ t ^ 2 = β t)
    (e : ℂ ≃L[ℝ] Schoenflies.Plane)
    (hK : Schoenflies.IsJordanCurve (e '' Set.range β))
    (hzero : (0 : Schoenflies.Plane) ∈ Schoenflies.inside (e '' Set.range β)) :
    γ 0 ≠ γ 1 := by
    have hobstruction (q : Schoenflies.Plane → Schoenflies.Plane) (hq : Continuous q)
      (t : Schoenflies.Plane ≃ₜ Schoenflies.Plane) (ht : ∀ x, t (t x) = x)
      (htzero : t 0 = 0) (hqzero : q 0 = 0)
      (hfiber : ∀ x y, q x = q y ↔ y = x ∨ y = t x)
      (C K : Set Schoenflies.Plane) (hC : Schoenflies.IsJordanCurve C)
      (hK : Schoenflies.IsJordanCurve K) (himage : q '' C = K)
      (hboundary : Disjoint C (t '' C)) (hzero : (0 : Schoenflies.Plane) ∈ Schoenflies.inside K) :
      False := by
      have hdisjoint (C : Set Schoenflies.Plane) (hC : Schoenflies.IsJordanCurve C)
        (t : Schoenflies.Plane ≃ₜ Schoenflies.Plane) (ht : ∀ x, t (t x) = x)
        (hboundary : Disjoint C (t '' C)) :
        Disjoint (Schoenflies.inside C ∪ C) (t '' (Schoenflies.inside C ∪ C)) := by
        let D := Schoenflies.inside C ∪ C
        have hsep := Schoenflies.jordan_curve_theorem hC
        have hDfront : frontier D = C := by
          have hD : D = (Schoenflies.outside C)ᶜ := by
            ext x
            constructor
            · rintro (hx | hx)
              · exact fun hxo => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hx hxo
              · exact fun hxo => Schoenflies.outside_subset_compl hxo hx
            · intro hx
              by_cases hxc : x ∈ C
              · exact Or.inr hxc
              · have hio : x ∈ Schoenflies.inside C ∪ Schoenflies.outside C := by
                  rw [Schoenflies.inside_union_outside]; exact hxc
                exact Or.inl (hio.resolve_right hx)
          rw [hD, frontier_compl, hsep.frontier_outside]
        have hDt : t '' (t '' D) = D := by
          rw [Set.image_image]
          have he : (fun x => t (t x)) = id := funext ht
          rw [he, Set.image_id]
        have hCne : C.Nonempty := by
          obtain ⟨f, hf, hfc⟩ := hC
          rw [← hfc]
          exact ⟨f 0, ⟨0, by norm_num, rfl⟩⟩
        have hneq : D ≠ t '' D := by
          intro he
          have hefront : C = t '' C := by
            calc C = frontier D := hDfront.symm
                 _ = frontier (t '' D) := congrArg frontier he
                 _ = t '' frontier D := (t.image_frontier D).symm
                 _ = t '' C := congrArg (fun A => t '' A) hDfront
          obtain ⟨x, hx⟩ := hCne
          exact Set.disjoint_left.mp hboundary hx (hefront ▸ hx)
        have hregionT : t '' D = Schoenflies.inside (t '' C) ∪ (t '' C) := by
          rw [Set.image_union, jordan_inside_homeomorph_image]
        rcases jordan_curve_closed_regions_disjoint_or_nested hC
            (jordan_curve_homeomorph_image hC t) hboundary with hd | h | h
        · simpa only [D, ← hregionT] using hd
        · rw [← hregionT] at h
          change D ⊆ t '' D at h
          have hrev : t '' D ⊆ D := by
            have hm := Set.image_mono h (f := t)
            simpa only [hDt] using hm
          exact False.elim (hneq (Set.Subset.antisymm h hrev))
        · rw [← hregionT] at h
          change t '' D ⊆ D at h
          have hrev : D ⊆ t '' D := by
            have hm := Set.image_mono h (f := t)
            simpa only [hDt] using hm
          exact False.elim (hneq (Set.Subset.antisymm hrev h))
      let D := Schoenflies.inside C ∪ C
      have hDdisj : Disjoint D (t '' D) := hdisjoint C hC t ht hboundary
      have hDzero : (0 : Schoenflies.Plane) ∉ D := by
        intro hz
        exact Set.disjoint_left.mp hDdisj hz ⟨0, hz, htzero⟩
      have hqinj : Set.InjOn q D := by
        intro x hx y hy hxy
        rcases (hfiber x y).mp hxy with he | he
        · exact he.symm
        · exact False.elim (Set.disjoint_left.mp hDdisj hy ⟨x, hx, he.symm⟩)
      obtain ⟨e, heb, hei⟩ := SpherePort.plane_inside_closed_disc_with_boundary C hC
      let d : C(Metric.closedBall (0 : Schoenflies.Plane) 1, Schoenflies.Plane) :=
        ⟨fun x => (e x).val, continuous_subtype_val.comp e.continuous⟩
      have hclosure : closure (Schoenflies.inside C) = D := by
        exact (Schoenflies.IsRegionOf.inside C).closure_eq
          (Schoenflies.jordan_curve_theorem hC)
      have hdrange : Set.range d = D := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact hclosure ▸ (e y).property
        · intro hx
          exact ⟨e.symm ⟨x, hclosure.symm ▸ hx⟩,
            congrArg Subtype.val (e.apply_symm_apply _)⟩
      let d' : C(Metric.closedBall (0 : Schoenflies.Plane) 1, Schoenflies.Plane) :=
        ⟨q ∘ d, hq.comp d.continuous⟩
      have hd'inj : Function.Injective d' := by
        intro x y hxy
        apply e.injective
        apply Subtype.ext
        exact hqinj (hdrange ▸ Set.mem_range_self x) (hdrange ▸ Set.mem_range_self y) hxy
      have hd'emb : Topology.IsEmbedding d' := d'.continuous.isClosedEmbedding hd'inj |>.isEmbedding
      have hbd : d' '' {x | (x : Schoenflies.Plane) ∈ Metric.sphere 0 1} = K := by
        rw [show d' = (⟨q, hq⟩ : C(Schoenflies.Plane, Schoenflies.Plane)).comp d by rfl]
        change (q ∘ d) '' _ = K
        rw [Set.image_comp]
        suffices hd : d '' {x | (x : Schoenflies.Plane) ∈ Metric.sphere 0 1} = C by
          rw [hd, himage]
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (heb y).mpr (by simpa [Metric.mem_sphere, dist_zero_right] using hy)
        · intro hx
          let y := e.symm ⟨x, hclosure.symm ▸ Or.inr hx⟩
          have hey : (e y).val = x := congrArg Subtype.val (e.apply_symm_apply _)
          refine ⟨y, ?_, hey⟩
          simpa [Metric.mem_sphere, dist_zero_right] using (heb y).mp (hey ▸ hx)
      have hdownregion := embedded_disc_range_eq_closed_inside d' hd'emb K hK hbd
      have hzRange : (0 : Schoenflies.Plane) ∈ Set.range d' := by
        rw [hdownregion]; exact Or.inl hzero
      obtain ⟨x, hx⟩ := hzRange
      have hd0 : d x = 0 := by
        rcases (hfiber (d x) 0).mp (hx.trans hqzero.symm) with he | he
        · exact he.symm
        · apply t.injective
          simpa only [htzero] using he.symm
      exact hDzero (hd0 ▸ (hdrange ▸ Set.mem_range_self x))
    have hloop {X : Type} [TopologicalSpace X] [T2Space X]
      (l : C(Interval, X)) (hend : l 0 = l 1)
      (hcoll : ∀ s t, l s = l t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
      ∃ c : Curve X, c.image = Set.range l := by
      let r := AddCircle.EndpointIdent (1 : ℝ) 0
      let j : Icc (0 : ℝ) (0 + 1) → Interval := fun t => ⟨t.val, by simpa only [zero_add] using t.property⟩
      have hj : Continuous j := continuous_subtype_val.subtype_mk _
      have hrespect : ∀ a b, r a b → l (j a) = l (j b) := by
        rintro a b ⟨⟩
        simpa [j] using hend
      let L : Quot r → X := Quot.lift (fun t => l (j t)) hrespect
      have hL : Continuous L := continuous_quot_lift _ (l.continuous.comp hj)
      have hLi : Function.Injective L := by
        intro a b
        induction a using Quot.inductionOn with | h a =>
          induction b using Quot.inductionOn with | h b =>
            intro hab
            rcases hcoll (j a) (j b) hab with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
            · apply congrArg (Quot.mk r)
              exact Subtype.ext (congrArg (fun t : Interval => t.val) he)
            · have ha' : a = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
              have hb' : b = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
              subst a; subst b
              exact Quot.sound AddCircle.EndpointIdent.mk
            · have ha' : a = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
              have hb' : b = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
              subst a; subst b
              exact (Quot.sound AddCircle.EndpointIdent.mk).symm
      let e : Circle ≃ₜ Quot r :=
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
          (AddCircle.homeoIccQuot (1 : ℝ) 0)
      let c : Curve X := ⟨L ∘ e, ((hL.comp e.continuous).isClosedEmbedding (hLi.comp e.injective)).isEmbedding⟩
      refine ⟨c, ?_⟩
      change range (L ∘ e) = range l
      rw [e.surjective.range_comp]
      ext x
      constructor
      · rintro ⟨q, rfl⟩
        induction q using Quot.inductionOn with | h t =>
          exact ⟨j t, rfl⟩
      · rintro ⟨t, rfl⟩
        exact ⟨Quot.mk r ⟨t.val, by simpa only [zero_add] using t.property⟩, rfl⟩
    intro hclosed
    let Γ : C(Interval, Schoenflies.Plane) := ⟨fun t => e (γ t), e.continuous.comp γ.continuous⟩
    have hΓends : Γ 0 = Γ 1 := congrArg e hclosed
    have hΓcoll (s t : Interval) (hst : Γ s = Γ t) :
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
      have hγ : γ s = γ t := e.injective hst
      exact hcoll s t (by rw [← hroot s, ← hroot t, hγ])
    obtain ⟨c, hc⟩ := hloop Γ hΓends hΓcoll
    let C := c.image
    let K := e '' Set.range β
    have hC : Schoenflies.IsJordanCurve C :=
      isJordanCurve_range_of_isEmbedding_circle ⟨c.map, c.embedded.continuous⟩ c.embedded
    let q : Schoenflies.Plane → Schoenflies.Plane := fun x => e ((e.symm x)^2)
    have hq : Continuous q := e.continuous.comp (e.symm.continuous.pow 2)
    let τ : Schoenflies.Plane ≃ₜ Schoenflies.Plane := Homeomorph.neg _
    have hτ (x) : τ (τ x) = x := neg_neg x
    have hτzero : τ 0 = 0 := neg_zero
    have hqzero : q 0 = 0 := by simp [q]
    have hfiber (x y) : q x = q y ↔ y = x ∨ y = τ x := by
      change e ((e.symm x)^2) = e ((e.symm y)^2) ↔ y = x ∨ y = -x
      rw [e.injective.eq_iff]
      constructor
      · intro hxy
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with he | he
        · exact Or.inl (e.symm.injective he.symm)
        · right
          apply e.symm.injective
          simpa using (congrArg Neg.neg he).symm
      · rintro (rfl | rfl)
        · rfl
        · simp
    have himage : q '' C = K := by
      rw [show C = Set.range Γ from hc]
      ext x
      constructor
      · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
        refine ⟨β t, Set.mem_range_self t, ?_⟩
        simp only [q, Γ, ContinuousMap.coe_mk, e.symm_apply_apply, hroot]
      · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
        refine ⟨Γ t, Set.mem_range_self t, ?_⟩
        simp only [q, Γ, ContinuousMap.coe_mk, e.symm_apply_apply, hroot]
    have hβne (t : Interval) : β t ≠ 0 := by
      intro he
      have hzK : (0 : Schoenflies.Plane) ∈ K := by
        exact ⟨β t, Set.mem_range_self t, by simp [he]⟩
      exact Schoenflies.inside_subset_compl hzero hzK
    have hboundary : Disjoint C (τ '' C) := by
      apply Set.disjoint_left.mpr
      intro x hx hxτ
      have hxrange : x ∈ Set.range Γ := by change x ∈ c.image at hx; rwa [hc] at hx
      obtain ⟨s, hs⟩ := hxrange
      obtain ⟨y, hy, hxy⟩ := hxτ
      have hyrange : y ∈ Set.range Γ := by change y ∈ c.image at hy; rwa [hc] at hy
      obtain ⟨t, ht⟩ := hyrange
      have hneg : γ s = -γ t := by
        apply e.injective
        simpa [Γ, τ, ← hs, ← ht] using hxy.symm
      have hβeq : β s = β t := by rw [← hroot s, ← hroot t, hneg, neg_sq]
      have hγself : γ s = -γ s := by
        rcases hcoll s t hβeq with he | ⟨hs0, ht1⟩ | ⟨hs1, ht0⟩
        · simpa only [he] using hneg
        · rw [hs0, ht1, ← hclosed] at hneg
          simpa only [hs0] using hneg
        · rw [hs1, ht0, hclosed] at hneg
          simpa only [hs1] using hneg
      have hγzero := CharZero.eq_neg_self_iff.mp hγself
      exact hβne s (by rw [← hroot s, hγzero]; norm_num)
    exact hobstruction q hq τ hτ hτzero hqzero hfiber C K hC hK himage hboundary hzero
  have hloop {X : Type} [TopologicalSpace X] [T2Space X]
    (l : C(Interval, X)) (hend : l 0 = l 1)
    (hcoll : ∀ s t, l s = l t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    ∃ c : Curve X, c.image = Set.range l := by
    let r := AddCircle.EndpointIdent (1 : ℝ) 0
    let j : Icc (0 : ℝ) (0 + 1) → Interval := fun t => ⟨t.val, by simpa only [zero_add] using t.property⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    have hrespect : ∀ a b, r a b → l (j a) = l (j b) := by
      rintro a b ⟨⟩
      simpa [j] using hend
    let L : Quot r → X := Quot.lift (fun t => l (j t)) hrespect
    have hL : Continuous L := continuous_quot_lift _ (l.continuous.comp hj)
    have hLi : Function.Injective L := by
      intro a b
      induction a using Quot.inductionOn with | h a =>
        induction b using Quot.inductionOn with | h b =>
          intro hab
          rcases hcoll (j a) (j b) hab with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · apply congrArg (Quot.mk r)
            exact Subtype.ext (congrArg (fun t : Interval => t.val) he)
          · have ha' : a = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
            have hb' : b = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
            subst a; subst b
            exact Quot.sound AddCircle.EndpointIdent.mk
          · have ha' : a = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
            have hb' : b = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
            subst a; subst b
            exact (Quot.sound AddCircle.EndpointIdent.mk).symm
    let e : Circle ≃ₜ Quot r :=
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
        (AddCircle.homeoIccQuot (1 : ℝ) 0)
    let c : Curve X := ⟨L ∘ e, ((hL.comp e.continuous).isClosedEmbedding (hLi.comp e.injective)).isEmbedding⟩
    refine ⟨c, ?_⟩
    change range (L ∘ e) = range l
    rw [e.surjective.range_comp]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Quot.inductionOn with | h t =>
        exact ⟨j t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Quot.mk r ⟨t.val, by simpa only [zero_add] using t.property⟩, rfl⟩
  have hiso : Nonempty (ℂ ≃ₗᵢ[ℝ] Schoenflies.Plane) := by
    let e : ℂ ≃L[ℝ] Schoenflies.Plane :=
      Complex.equivRealProdCLM.trans ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
        (EuclideanSpace.equiv (Fin 2) ℝ).symm)
    have hnorm (z : ℂ) : ‖e z‖ = ‖z‖ := by
      have he0 : e z 0 = z.re := rfl
      have he1 : e z 1 = z.im := rfl
      have heSq : ‖e z‖^2 = ‖z‖^2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Complex.sq_norm]
        simp [Fin.sum_univ_two, he0, he1, Complex.normSq_apply, pow_two]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heSq
    exact ⟨{ toLinearEquiv := e.toLinearEquiv, norm_map' := hnorm }⟩
  classical
  let D := Metric.closedBall (0 : Schoenflies.Plane) 1
  have hβnorm (t : Interval) : ‖(β t).val‖ = 1 := by
    have ht : β t ∈ {z | ‖z.val‖ = 1} := hrange ▸ Set.mem_range_self t
    exact ht
  obtain ⟨w, hw⟩ := M.cover.projection_surjective (f m)
  have hwbranch : M.cover.projection w ∈ M.cover.branch := hw ▸ (honly m).mpr rfl
  let c := M.cover.branch_chart w hwbranch
  have hcdown : c.downstairs (f m) = 0 := hw ▸ c.downstairs_center
  have hcdownsrc : f m ∈ c.downstairs.source := hw ▸ c.downstairs_mem
  have hcUpZero : (0 : ℂ) ∈ c.upstairs.target := by
    simpa [c.upstairs_center] using c.upstairs.map_source c.upstairs_mem
  obtain ⟨ρ, hρ, hρball⟩ := Metric.isOpen_iff.mp c.upstairs.open_target 0 hcUpZero
  let r := ρ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrBall : Metric.closedBall (0 : ℂ) r ⊆ c.upstairs.target := by
    intro z hz
    apply hρball
    change dist z 0 ≤ r at hz
    change dist z 0 < ρ
    exact lt_of_le_of_lt hz (by dsimp [r]; linarith)
  let O := c.downstairs.source ∩ c.downstairs ⁻¹' Metric.ball (0 : ℂ) (r^2)
  have hO : IsOpen O := c.downstairs.isOpen_inter_preimage Metric.isOpen_ball
  have hmO : f m ∈ O := ⟨hcdownsrc, by
    rw [Set.mem_preimage, hcdown]; simp [Metric.mem_ball, sq_pos_of_pos hr]⟩
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (f.continuous.continuousAt.preimage_mem_nhds (hO.mem_nhds hmO))
  let δ := min (ε / 4) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδle : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : 2 * δ < ε := by
    have hle := min_le_left (ε/4) (1/2 : ℝ)
    change δ ≤ ε/4 at hle
    linarith
  let T : Interval → D → D := fun a z => ⟨(1-(a : ℝ)) • m.val + (a : ℝ) • z.val,
    (convex_closedBall (0 : Schoenflies.Plane) 1) m.property z.property
      (sub_nonneg.mpr a.property.2) a.property.1 (by ring)⟩
  let d : Interval := ⟨δ, by constructor; exact hδ.le; linarith⟩
  have hTcont : Continuous (fun z : Interval × D => T z.1 z.2) :=
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul continuous_const).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hTinj (a : Interval) (ha : 0 < (a : ℝ)) : Function.Injective (T a) := by
    intro x y hxy
    apply Subtype.ext
    have he := congrArg Subtype.val hxy
    change (1-(a : ℝ)) • m.val + (a : ℝ) • x.val =
      (1-(a : ℝ)) • m.val + (a : ℝ) • y.val at he
    exact smul_right_injective Schoenflies.Plane (ne_of_gt ha) (add_left_cancel he)
  have hTm (a : Interval) : T a m = m := by
    apply Subtype.ext
    change (1-(a : ℝ)) • m.val + (a : ℝ) • m.val = m.val
    rw [← add_smul]
    simp
  have hT1 (z : D) : T 1 z = z := by apply Subtype.ext; simp [T]
  have hTsmall (z : D) : f (T d z) ∈ O := by
    apply hεball
    change dist (T d z) m < ε
    rw [Subtype.dist_eq, dist_eq_norm]
    have he : (T d z).val - m.val = δ • (z.val - m.val) := by
      dsimp [T, d]
      module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    have hzNorm : ‖z.val‖ ≤ 1 := by
      have hz := z.property
      change dist z.val 0 ≤ 1 at hz
      simpa only [dist_zero_right] using hz
    have hdiff := norm_sub_le z.val m.val
    exact lt_of_le_of_lt (by nlinarith [norm_nonneg z.val, norm_nonneg m.val]) hδε
  obtain ⟨e⟩ := hiso
  let fD : C(D, S) := ⟨fun z => f (T d z),
    f.continuous.comp (hTcont.comp (continuous_const.prodMk continuous_id))⟩
  have hdowncont : Continuous (fun z => c.downstairs (fD z)) :=
    c.downstairs.continuousOn.comp_continuous fD.continuous (fun z => (hTsmall z).1)
  let A : C(D, Schoenflies.Plane) := ⟨fun z => e (c.downstairs (fD z)),
    e.continuous.comp hdowncont⟩
  have hAinj : Function.Injective A := by
    intro x y hxy
    apply hTinj d hδ
    apply hf.injective
    exact c.downstairs.injOn (hTsmall x).1 (hTsmall y).1 (e.injective hxy)
  have hAemb : IsEmbedding A := (A.continuous.isClosedEmbedding hAinj).isEmbedding
  have hAm : A m = 0 := by
    simp only [A, fD, ContinuousMap.coe_mk, hTm, hcdown, map_zero]
  let B : C(Interval, Schoenflies.Plane) := A.comp β
  have hBends : B 0 = B 1 := congrArg A hends
  have hBcoll (s t : Interval) (hst : B s = B t) := hcoll s t (hAinj hst)
  obtain ⟨cB, hcB⟩ := hloop B hBends hBcoll
  let K := Set.range B
  have hK : Schoenflies.IsJordanCurve K := by
    rw [show K = cB.image from hcB.symm]
    exact isJordanCurve_range_of_isEmbedding_circle ⟨cB.map, cB.embedded.continuous⟩ cB.embedded
  have hAboundary : A '' {z : D | (z : Schoenflies.Plane) ∈ Metric.sphere 0 1} = K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hznorm : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right, Set.mem_ofPred_eq] using hz
      obtain ⟨t, ht⟩ := hrange.symm ▸ (show z ∈ {z : D | ‖z.val‖ = 1} from hznorm)
      exact ⟨t, congrArg A ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨β t, by simpa only [Metric.mem_sphere, dist_zero_right, Set.mem_ofPred_eq] using hβnorm t, rfl⟩
  have hKzero : (0 : Schoenflies.Plane) ∉ K := by
    rintro ⟨t, ht⟩
    have hβm : β t = m := hAinj (ht.trans hAm.symm)
    have hnorm := hβnorm t
    rw [hβm] at hnorm
    linarith
  have hzeroInside : (0 : Schoenflies.Plane) ∈ Schoenflies.inside K := by
    have hregions := embedded_disc_range_eq_closed_inside A hAemb K hK hAboundary
    have hz : (0 : Schoenflies.Plane) ∈ Set.range A := ⟨m, hAm⟩
    rw [hregions] at hz
    exact hz.resolve_right hKzero
  have hγne : γ 0 ≠ γ 1 := by
    intro hγclosed
    let k : Interval → Interval := fun s => ⟨δ + (1-δ)*(s : ℝ), by
      constructor
      · nlinarith [s.property.1]
      · nlinarith [s.property.2]⟩
    have hkcont : Continuous k :=
      (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _
    have hk0 : k 0 = d := by apply Subtype.ext; simp [k, d]
    have hk1 : k 1 = 1 := by apply Subtype.ext; simp [k]
    have hkpos (s : Interval) : 0 < (k s : ℝ) := by
      dsimp [k]
      nlinarith [s.property.1]
    let H : C(Interval × Interval, S) := ⟨fun z => f (T (k z.1) (β z.2)),
      f.continuous.comp (hTcont.comp ((hkcont.comp continuous_fst).prodMk
        (β.continuous.comp continuous_snd)))⟩
    have hHloop (s) : H (s,0) = H (s,1) := congrArg (fun z => f (T (k s) z)) hends
    have hHavoid (z : Interval × Interval) : H z ∉ M.cover.branch := by
      intro hb
      have he : T (k z.1) (β z.2) = m := (honly _).mp hb
      have hβm : β z.2 = m := hTinj _ (hkpos _) (he.trans (hTm _).symm)
      have hn := hβnorm z.2
      rw [hβm] at hn
      linarith
    have hHγ (t) : M.cover.projection (γ t) = H (1,t) := by
      change M.cover.projection (γ t) = f (T (k 1) (β t))
      rw [hk1, hT1]
      exact hγπ t
    obtain ⟨η, hηπH, hηends⟩ := hfreeLoop H hHloop hHavoid γ hHγ hγclosed
    have hηπ (t) : M.cover.projection (η t) = fD (β t) := by
      have he := hηπH t
      change M.cover.projection (η t) = f (T (k 0) (β t)) at he
      rw [hk0] at he
      exact he
    have hBne (t) : c.downstairs (fD (β t)) ≠ 0 := by
      intro he
      apply hKzero
      refine ⟨t, ?_⟩
      change e (c.downstairs (fD (β t))) = 0
      rw [he, map_zero]
    have hηsrc (t) : η t ∈ c.upstairs.source := by
      exact (hsmallFiber w hwbranch r hr hrBall (fD (β t))
        (hTsmall (β t)).1 (by
          have hn := (hTsmall (β t)).2
          have hnorm : ‖c.downstairs (fD (β t))‖ < r^2 := by
            change dist (c.downstairs (fD (β t))) 0 < r^2 at hn
            simpa only [dist_zero_right] using hn
          exact hnorm.le) (hBne t)).2 (η t) (hηπ t)
    let βC : C(Interval, ℂ) := ⟨fun t => c.downstairs (fD (β t)), hdowncont.comp β.continuous⟩
    let ηC : C(Interval, ℂ) := ⟨fun t => c.upstairs (η t),
      c.upstairs.continuousOn.comp_continuous η.continuous hηsrc⟩
    have hroot (t) : ηC t ^ 2 = βC t := by
      change c.upstairs (η t)^2 = c.downstairs (fD (β t))
      rw [← c.square _ (hηsrc t), hηπ]
    have hβCcoll (s t : Interval) (hst : βC s = βC t) :
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) :=
      hBcoll s t (congrArg e hst)
    have hCimage : e.toContinuousLinearEquiv '' Set.range βC = K := by
      ext x
      constructor
      · rintro ⟨y, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩
      · rintro ⟨t, rfl⟩; exact ⟨βC t, Set.mem_range_self t, rfl⟩
    have hK' : Schoenflies.IsJordanCurve (e.toContinuousLinearEquiv '' Set.range βC) :=
      hCimage.symm ▸ hK
    have hzero' : (0 : Schoenflies.Plane) ∈
        Schoenflies.inside (e.toContinuousLinearEquiv '' Set.range βC) := hCimage.symm ▸ hzeroInside
    have hnotclosed := hsquare βC ηC hβCcoll hroot e.toContinuousLinearEquiv hK' hzero'
    exact hnotclosed (congrArg c.upstairs hηends)
  have hprojends : M.cover.projection (γ 0) = M.cover.projection (γ 1) :=
    (hγπ 0).trans ((congrArg f hends).trans (hγπ 1).symm)
  rcases (M.cover.fiber_pair (γ 0) (γ 1)).mp hprojends with he | he
  · exact False.elim (hγne he.symm)
  · exact he
end CurveComplex.HyperellipticModel
