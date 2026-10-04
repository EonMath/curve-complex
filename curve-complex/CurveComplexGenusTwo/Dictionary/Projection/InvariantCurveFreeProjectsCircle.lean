import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
set_option maxHeartbeats 4000000
theorem invariant_curve_avoiding_branch_projects_punctured_circle (c : Curve E) (hc : M.cover.deck '' c.image = c.image)
    (hbranch : ∀ t, M.cover.projection (c.map t) ∉ M.cover.branch) :
    ∃ a : PuncturedCircle M,
      c.image = M.cover.projection ⁻¹' a.image ∧ a.image = M.cover.projection '' c.image := by
  have hInvolution (c : Curve E) (hc : M.cover.deck '' c.image = c.image) :
      ∃ j : Circle ≃ₜ Circle,
        (∀ t, c.map (j t) = M.cover.deck (c.map t)) ∧
        Function.Involutive j ∧
        (∀ t, j t = t ↔ M.cover.projection (c.map t) ∈ M.cover.branch) ∧
        ∃ t, j t ≠ t := by
          as_aux_lemma =>
      have hConstruct (c : Curve E) (hc : M.cover.deck '' c.image = c.image) :
          ∃ j : Circle ≃ₜ Circle,
            (∀ t, c.map (j t) = M.cover.deck (c.map t)) ∧
            Function.Involutive j ∧
            (∀ t, j t = t ↔ M.cover.projection (c.map t) ∈ M.cover.branch) := by
        let h := c.embedded.toHomeomorph
        have hmem (x : c.image) : M.cover.deck x.val ∈ c.image := by
          exact hc.subset (Set.mem_image_of_mem M.cover.deck x.property)
        let d : c.image ≃ₜ c.image :=
          { toFun := fun x => ⟨M.cover.deck x.val,hmem x⟩
            invFun := fun x => ⟨M.cover.deck x.val,hmem x⟩
            left_inv := fun x => Subtype.ext (M.cover.deck_involution x.val)
            right_inv := fun x => Subtype.ext (M.cover.deck_involution x.val)
            continuous_toFun := (M.cover.deck.continuous.comp continuous_subtype_val).subtype_mk _
            continuous_invFun := (M.cover.deck.continuous.comp continuous_subtype_val).subtype_mk _ }
        let j := h.trans (d.trans h.symm)
        have hj (t) : c.map (j t) = M.cover.deck (c.map t) := by
          have hh := h.apply_symm_apply (d (h t))
          exact congrArg Subtype.val hh
        refine ⟨j,hj,?_,?_⟩
        · intro t
          apply c.embedded.injective
          rw [hj,hj,M.cover.deck_involution]
        · intro t
          constructor
          · intro ht
            apply (M.cover.fixed_iff_branch (c.map t)).mp
            rw [← hj,ht]
          · intro ht
            apply c.embedded.injective
            rw [hj,(M.cover.fixed_iff_branch (c.map t)).mpr ht]
    
      classical
      obtain ⟨j,hj,hi,hfix⟩ := hConstruct c hc
      refine ⟨j,hj,hi,hfix,?_⟩
      by_contra hn
      push Not at hn
      have : Infinite (Set.Icc (0 : ℝ) 1) := Set.Icc.infinite (by norm_num)
      have : Infinite Circle := Infinite.of_injective
        (fun t : Set.Icc (0 : ℝ) 1 => Circle.exp t.val) (by
          intro t u h
          apply Subtype.ext
          exact Circle.exp_injOn_Icc (by linarith [Real.pi_gt_three]) t.property u.property h)
      have hπinj : Function.Injective (M.cover.projection ∘ c.map) := by
        intro s t he
        rcases (M.cover.fiber_pair (c.map s) (c.map t)).mp he with hh | hh
        · exact c.embedded.injective hh.symm
        · have hs : M.cover.deck (c.map s) = c.map s := by rw [← hj,hn s]
          exact c.embedded.injective (hh.trans hs).symm
      have hfin := M.cover.branch.finite_toSet.preimage hπinj.injOn
      have hall : (M.cover.projection ∘ c.map) ⁻¹' (M.cover.branch : Set S) = Set.univ := by
        ext t
        simp only [Set.mem_preimage,Set.mem_univ,iff_true,Function.comp_apply]
        exact (hfix t).mp (hn t)
      rw [hall] at hfin
      exact Set.infinite_univ hfin
  
  have hExchange (p q : Circle) (hpq : p ≠ q) (j : Circle ≃ₜ Circle)
      (hinv : Function.Involutive j) (hpair : j '' {p,q} = {p,q})
      (hno : ∀ t : unitInterval, t ∈ Ioo 0 1 → j (Circle.path p q t) ≠ Circle.path p q t) :
      j '' Set.range (Circle.path p q) = Set.range (Circle.path q p) ∧
        Set.range (Circle.path p q) ∪ j '' Set.range (Circle.path p q) = Set.univ ∧
        Set.range (Circle.path p q) ∩ j '' Set.range (Circle.path p q) = {p,q} := by
          as_aux_lemma =>
      have hPerm (p q : Circle) (hpq : p ≠ q) (j : Circle ≃ₜ Circle)
          (hinv : Function.Involutive j) (hpair : j '' ({p,q} : Set Circle) = ({p,q} : Set Circle)) :
          j '' Set.range (Circle.path p q) = Set.range (Circle.path p q) ∨
          j '' Set.range (Circle.path p q) = Set.range (Circle.path q p) := by
            as_aux_lemma =>
          have hSides (p q : Circle) (hpq : p ≠ q) :
              let P := Circle.path p q
              let Q := Circle.path q p
              let U := (Set.range Q)ᶜ
              let V := (Set.range P)ᶜ
              IsOpen U ∧ IsOpen V ∧ IsPreconnected U ∧ IsPreconnected V ∧
                U.Nonempty ∧ V.Nonempty ∧ Disjoint U V ∧ U ∪ V = ({p,q} : Set Circle)ᶜ ∧
                closure U = Set.range P ∧ closure V = Set.range Q := by
            dsimp only
            have hPclosed := (isCompact_range (Circle.path p q).continuous).isClosed
            have hQclosed := (isCompact_range (Circle.path q p).continuous).isClosed
            have hPU : (Set.range (Circle.path q p))ᶜ = (Circle.path p q) '' Ioo 0 1 :=
              Circle.compl_range_path hpq.symm
            have hQV : (Set.range (Circle.path p q))ᶜ = (Circle.path q p) '' Ioo 0 1 :=
              Circle.compl_range_path hpq
            have hcl (x y : Circle) :
                closure ((Circle.path x y) '' Ioo 0 1) = Set.range (Circle.path x y) := by
              rw [(Circle.path x y).continuous.isClosedMap.closure_image_eq_of_continuous
                (Circle.path x y).continuous,closure_Ioo (by norm_num : (0 : unitInterval) ≠ 1),
                ← unitInterval.univ_eq_Icc,Set.image_univ]
            refine ⟨hQclosed.isOpen_compl,hPclosed.isOpen_compl,?_,?_,?_,?_,?_,?_,?_,?_⟩
            · rw [hPU]; exact isPreconnected_Ioo.image _ (Circle.path p q).continuous.continuousOn
            · rw [hQV]; exact isPreconnected_Ioo.image _ (Circle.path q p).continuous.continuousOn
            · rw [hPU]; exact (Set.nonempty_Ioo.mpr (by norm_num : (0 : unitInterval) < 1)).image _
            · rw [hQV]; exact (Set.nonempty_Ioo.mpr (by norm_num : (0 : unitInterval) < 1)).image _
            · rw [Set.disjoint_iff_inter_eq_empty,← Set.compl_union,
                Circle.range_path_union_range_path hpq.symm,compl_univ]
            · rw [← Set.compl_inter,Set.inter_comm,Circle.range_path_inter_range_path hpq]
            · rw [hPU,hcl]
            · rw [hQV,hcl]
      
          let P := Circle.path p q
          let Q := Circle.path q p
          let U := (Set.range Q)ᶜ
          let V := (Set.range P)ᶜ
          obtain ⟨hUo,hVo,hUc,hVc,hUn,hVn,hdisj,hUV,hclU,hclV⟩ := hSides p q hpq
          have hcover (W : Set Circle) (hW : W ⊆ U ∪ V) : j '' W ⊆ U ∪ V := by
            rintro z ⟨x,hx,rfl⟩
            have hxn : x ∉ (({p,q} : Set Circle) : Set Circle) := by
              change x ∈ ({p,q} : Set Circle)ᶜ
              rw [← hUV]
              exact hW hx
            have hjn : j x ∉ (({p,q} : Set Circle) : Set Circle) := by
              intro hb
              have hh : j (j x) ∈ ({p,q} : Set Circle) := hpair.subset ⟨j x,hb,rfl⟩
              rw [hinv] at hh
              exact hxn hh
            rw [hUV]
            exact hjn
          have hJU := hcover U subset_union_left
          have hJV := hcover V subset_union_right
          have hsideU := (hUc.image j j.continuous.continuousOn).subset_or_subset hUo hVo hdisj hJU
          rcases hsideU with hs | hs
          · have he : j '' U = U := by
              apply subset_antisymm hs
              intro x hx
              exact ⟨j x,hs ⟨x,hx,rfl⟩,hinv x⟩
            left
            rw [← hclU,j.image_closure,he,hclU]
          · have hUJV : U ⊆ j '' V := by
              intro x hx
              have hjx := hJU ⟨x,hx,rfl⟩
              rcases hjx with hjx | hjx
              · have hxV : x ∈ V := by
                  have hh := hs ⟨j x,hjx,rfl⟩
                  change j (j x) ∈ V at hh
                  rw [hinv x] at hh
                  exact hh
                exact False.elim (Set.disjoint_left.mp hdisj hx hxV)
              · exact ⟨j x,hjx,hinv x⟩
            have hsideV := (hVc.image j j.continuous.continuousOn).subset_or_subset hUo hVo hdisj hJV
            have hJVU : j '' V ⊆ U := by
              rcases hsideV with hv | hv
              · exact hv
              · obtain ⟨x,hx⟩ := hUn
                exact False.elim (Set.disjoint_left.mp hdisj hx (hv (hUJV hx)))
            have he : j '' U = V := by
              apply subset_antisymm hs
              intro x hx
              exact ⟨j x,hJVU ⟨x,hx,rfl⟩,hinv x⟩
            right
            rw [← hclU,j.image_closure,he,hclV]
    
      have hFix (g : C(unitInterval,unitInterval)) (hinv : Function.Involutive g) :
          ∃ t : unitInterval, t ∈ Ioo 0 1 ∧ g t = t := by
            as_aux_lemma =>
          have hi : Function.Injective g := hinv.injective
          rcases g.continuous.strictMono_of_inj hi with hm | ha
          · have he (t : unitInterval) : g t = t := by
              rcases lt_trichotomy (g t) t with hh | hh | hh
              · have hk := hm hh
                rw [hinv t] at hk
                exact False.elim (lt_asymm hh hk)
              · exact hh
              · have hk := hm hh
                rw [hinv t] at hk
                exact False.elim (lt_asymm hh hk)
            let t : unitInterval := ⟨1/2,by norm_num⟩
            refine ⟨t,?_,he t⟩
            constructor
            · change (0:ℝ) < 1/2; norm_num
            · change (1/2:ℝ) < 1; norm_num
          · have h01 : g 1 < g 0 := ha (by norm_num : (0:unitInterval) < 1)
            have hn0 : g 0 ≠ 0 := by
              intro he
              rw [he] at h01
              exact not_lt_of_ge (g 1).property.1 h01
            have hn1 : g 1 ≠ 1 := by
              intro he
              rw [he] at h01
              exact not_lt_of_ge (g 0).property.2 h01
            let F : unitInterval → ℝ := fun t => (g t : ℝ) - (t : ℝ)
            have hc : Continuous F := (continuous_subtype_val.comp g.continuous).sub continuous_subtype_val
            have hF0 : 0 ≤ F 0 := by
              change 0 ≤ (g 0 : ℝ) - 0
              simpa only [sub_zero] using (g 0).property.1
            have hF1 : F 1 ≤ 0 := by
              change (g 1 : ℝ) - 1 ≤ 0
              exact sub_nonpos.mpr (g 1).property.2
            obtain ⟨t,_,ht⟩ := intermediate_value_Icc' (by norm_num : (0:unitInterval) ≤ 1)
              hc.continuousOn ⟨hF1,hF0⟩
            have hfix : g t = t := Subtype.ext (sub_eq_zero.mp ht)
            refine ⟨t,⟨?_,?_⟩,hfix⟩
            · apply lt_of_le_of_ne t.property.1
              intro he
              have ht0 : t = 0 := Subtype.ext he.symm
              exact hn0 (by simpa only [ht0] using hfix)
            · apply lt_of_le_of_ne t.property.2
              intro he
              have ht1 : t = 1 := Subtype.ext he
              exact hn1 (by simpa only [ht1] using hfix)
    
      have hex : j '' Set.range (Circle.path p q) = Set.range (Circle.path q p) := by
        rcases hPerm p q hpq j hinv hpair with he | he
        · let P := Circle.path p q
          have hPi : Function.Injective P := Circle.path_injective_of_ne hpq
          have hPe : IsEmbedding P := (P.continuous.isClosedEmbedding hPi).isEmbedding
          let h := hPe.toHomeomorph
          have hmem (x : Set.range P) : j x.val ∈ Set.range P :=
            he.subset (Set.mem_image_of_mem j x.property)
          let d : Set.range P ≃ₜ Set.range P :=
            { toFun := fun x => ⟨j x.val,hmem x⟩
              invFun := fun x => ⟨j x.val,hmem x⟩
              left_inv := fun x => Subtype.ext (hinv x.val)
              right_inv := fun x => Subtype.ext (hinv x.val)
              continuous_toFun := (j.continuous.comp continuous_subtype_val).subtype_mk _
              continuous_invFun := (j.continuous.comp continuous_subtype_val).subtype_mk _ }
          let g := h.trans (d.trans h.symm)
          have hg (t) : P (g t) = j (P t) := congrArg Subtype.val (h.apply_symm_apply (d (h t)))
          have hgi : Function.Involutive g := by
            intro t
            apply hPi
            rw [hg,hg,hinv]
          obtain ⟨t,ht,hfix⟩ := hFix ⟨g,g.continuous⟩ hgi
          exact False.elim (hno t ht ((hg t).symm.trans (congrArg P hfix)))
        · exact he
      refine ⟨hex,?_,?_⟩
      · rw [hex,Circle.range_path_union_range_path hpq]
      · rw [hex,Circle.range_path_inter_range_path hpq]
  
  have hLoop {X : Type} [TopologicalSpace X] [T2Space X]
      (l : C(Interval, X)) (hend : l 0 = l 1)
      (hcoll : ∀ s t, l s = l t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
      ∃ c : Curve X, c.image = Set.range l := by
    let r := AddCircle.EndpointIdent (1 : ℝ) 0
    let j : Icc (0 : ℝ) (0 + 1) → Interval := fun t => ⟨t.val, by simpa using t.property⟩
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
      exact ⟨Quot.mk r ⟨t.val, by simp⟩, rfl⟩
  
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨j,hj,hi,hfix,_⟩ := hInvolution c hc
  have hfree (t) : j t ≠ t := fun he => hbranch t ((hfix t).mp he)
  let p : Circle := 1
  let q := j p
  have hpq : p ≠ q := (hfree p).symm
  let P := Circle.path p q
  have hPi : Function.Injective P := Circle.path_injective_of_ne hpq
  have hjp : j p = q := rfl
  have hjq : j q = p := hi p
  have hpair : j '' ({p,q}:Set Circle) = {p,q} := by
    simp only [Set.image_insert_eq,Set.image_singleton,hjp,hjq,Set.pair_comm]
  obtain ⟨hex,hcover,hinter⟩ := hExchange p q hpq j hi hpair (fun t _ => hfree (P t))
  let β : C(Interval,S) := ⟨fun t => M.cover.projection (c.map (P t)),
    M.cover.projection_continuous.comp (c.embedded.continuous.comp P.continuous)⟩
  have hends : β 0 = β 1 := by
    change M.cover.projection (c.map (P 0)) = M.cover.projection (c.map (P 1))
    rw [P.source,P.target,← hjp,hj,M.cover.projection_deck]
  have hcoll : ∀ s t, β s = β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
    intro s t he
    rcases (M.cover.fiber_pair (c.map (P s)) (c.map (P t))).mp he with he | he
    · exact Or.inl (hPi (c.embedded.injective he)).symm
    · have hJ : P t = j (P s) := c.embedded.injective (he.trans (hj (P s)).symm)
      have hpT : P t ∈ Set.range P ∩ j '' Set.range P :=
        ⟨⟨t,rfl⟩,⟨P s,⟨s,rfl⟩,hJ.symm⟩⟩
      rw [hinter] at hpT
      have hST : P s = j (P t) := by rw [hJ,hi]
      rcases hpT with heT | heT
      · have ht0 : t=0 := hPi (heT.trans P.source.symm)
        have hs1 : s=1 := hPi ((hST.trans (congrArg j heT)).trans (hjp.trans P.target.symm))
        exact Or.inr (Or.inr ⟨hs1,ht0⟩)
      · have ht1 : t=1 := hPi (heT.trans P.target.symm)
        have hs0 : s=0 := hPi ((hST.trans (congrArg j heT)).trans (hjq.trans P.source.symm))
        exact Or.inr (Or.inl ⟨hs0,ht1⟩)
  obtain ⟨d,hd⟩ := hLoop β hends hcoll
  have hβimage : Set.range β = M.cover.projection '' c.image := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨c.map (P t),⟨P t,rfl⟩,rfl⟩
    · rintro ⟨y,⟨t,rfl⟩,rfl⟩
      have ht : t ∈ Set.range P ∪ j '' Set.range P := by rw [hcover]; trivial
      rcases ht with ⟨s,he⟩ | ⟨w,⟨s,rfl⟩,he⟩
      · exact ⟨s,congrArg (M.cover.projection ∘ c.map) he⟩
      · refine ⟨s,?_⟩
        change M.cover.projection (c.map (P s)) = M.cover.projection (c.map t)
        rw [← he,hj,M.cover.projection_deck]
  have havoid : Disjoint d.image (M.cover.branch : Set S) := by
    apply Set.disjoint_left.mpr
    intro z hz hb
    rw [hd] at hz
    obtain ⟨t,rfl⟩ := hz
    exact hbranch (P t) hb
  let a : PuncturedCircle M := ⟨d,havoid⟩
  have ha : a.image = M.cover.projection '' c.image := hd.trans hβimage
  refine ⟨a,?_,ha⟩
  rw [ha]
  ext x
  constructor
  · intro hx
    exact ⟨x,hx,rfl⟩
  · rintro ⟨y,hy,hπ⟩
    rcases (M.cover.fiber_pair y x).mp hπ with he | he
    · exact he ▸ hy
    · rw [he]
      exact hc.subset (Set.mem_image_of_mem M.cover.deck hy)
end CurveComplex.HyperellipticModel
