import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
theorem invariant_curve_meeting_branch_projects_nonloop_arc (c : Curve E) (hc : M.cover.deck '' c.image = c.image)
    (hbranch : ∃ t, M.cover.projection (c.map t) ∈ M.cover.branch) :
    ∃ a : NonLoopArc M, c.image = M.cover.projection ⁻¹' a.image := by
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
  
  have hClassify (j : Circle ≃ₜ Circle) (hinv : Function.Involutive j)
      (hne : ∃ z, j z ≠ z) (p : Circle) (hp : j p = p) :
      ∃ q : Circle, q ≠ p ∧ j q = q ∧
        ∀ z, j z = z ↔ z = p ∨ z = q := by
          as_aux_lemma =>
      have hNeg (j : Circle ≃ₜ Circle) (hinv : Function.Involutive j)
          (hneg : j (-1) = -1) (hne : ∃ z, j z ≠ z) :
          ∃ q : Circle, q ≠ -1 ∧ j q = q ∧
            ∀ z, j z = z ↔ z = -1 ∨ z = q := by
              as_aux_lemma =>
          have hChart (j : Circle ≃ₜ Circle) (hinv : Function.Involutive j)
              (hneg : j (-1) = -1) (hne : ∃ z, j z ≠ z) :
              ∃ f : ℝ → ℝ,
                ContinuousOn f (Ioo (-Real.pi) Real.pi) ∧
                MapsTo f (Ioo (-Real.pi) Real.pi) (Ioo (-Real.pi) Real.pi) ∧
                (∀ x ∈ Ioo (-Real.pi) Real.pi, f (f x) = x) ∧
                (∀ x ∈ Ioo (-Real.pi) Real.pi, Circle.exp (f x) = j (Circle.exp x)) ∧
                ∃ x ∈ Ioo (-Real.pi) Real.pi, f x ≠ x := by
            have hnegarg : Complex.arg ((-1 : Circle) : ℂ) = Real.pi := by simp
            have harg {z : Circle} (hz : z ≠ -1) : Complex.arg (z : ℂ) ∈ Ioo (-Real.pi) Real.pi := by
              refine ⟨Complex.neg_pi_lt_arg _,lt_of_le_of_ne (Complex.arg_le_pi _) ?_⟩
              intro he
              apply hz
              exact Circle.injective_arg (he.trans hnegarg.symm)
            have hexp {x : ℝ} (hx : x ∈ Ioo (-Real.pi) Real.pi) : Circle.exp x ≠ -1 := by
              intro he
              have hh := congrArg (fun z : Circle => Complex.arg (z : ℂ)) he
              rw [Circle.arg_exp hx.1 hx.2.le,hnegarg] at hh
              exact (ne_of_lt hx.2) hh
            have hjexp {x : ℝ} (hx : x ∈ Ioo (-Real.pi) Real.pi) : j (Circle.exp x) ≠ -1 := by
              intro he
              exact hexp hx (j.injective (he.trans hneg.symm))
            let f : ℝ → ℝ := fun x => Complex.arg (j (Circle.exp x) : ℂ)
            have hmap : MapsTo f (Ioo (-Real.pi) Real.pi) (Ioo (-Real.pi) Real.pi) :=
              fun _ hx => harg (hjexp hx)
            have hcomp : Continuous (fun x : ℝ => (j (Circle.exp x) : ℂ)) :=
              continuous_subtype_val.comp (j.continuous.comp Circle.exp.continuous)
            have hslit : MapsTo (fun x : ℝ => (j (Circle.exp x) : ℂ))
                (Ioo (-Real.pi) Real.pi) Complex.slitPlane := by
              intro x hx
              exact Complex.mem_slitPlane_iff_arg.mpr ⟨ne_of_lt (hmap hx).2,(j (Circle.exp x)).coe_ne_zero⟩
            refine ⟨f,Complex.continuousOn_arg.comp hcomp.continuousOn hslit,hmap,?_,?_,?_⟩
            · intro x hx
              change Complex.arg (j (Circle.exp (Complex.arg (j (Circle.exp x) : ℂ))) : ℂ) = x
              rw [Circle.exp_arg,hinv,Circle.arg_exp hx.1 hx.2.le]
            · intro x _
              exact Circle.exp_arg _
            · obtain ⟨z,hz⟩ := hne
              have hzneg : z ≠ -1 := by rintro rfl; exact hz hneg
              refine ⟨Complex.arg (z : ℂ),harg hzneg,?_⟩
              intro he
              apply hz
              apply Circle.injective_arg
              simpa only [f,Circle.exp_arg] using he
      
          have hInterval (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
              (hf : ContinuousOn f (Ioo a b)) (hmap : MapsTo f (Ioo a b) (Ioo a b))
              (hinv : ∀ x ∈ Ioo a b, f (f x) = x)
              (hne : ∃ x ∈ Ioo a b, f x ≠ x) :
              StrictAntiOn f (Ioo a b) ∧ ∃! x, x ∈ Ioo a b ∧ f x = x := by
            have hi : InjOn f (Ioo a b) := by
              intro x hx y hy he
              rw [← hinv x hx,← hinv y hy,he]
            have ha : StrictAntiOn f (Ioo a b) := by
              rcases hf.strictMonoOn_of_injOn_Ioo hab hi with hm | hm
              · obtain ⟨x,hx,hne⟩ := hne
                rcases lt_or_gt_of_ne hne with hlt | hlt
                · have hh := hm (hmap hx) hx hlt
                  rw [hinv x hx] at hh
                  exact False.elim (lt_asymm hlt hh)
                · have hh := hm hx (hmap hx) hlt
                  rw [hinv x hx] at hh
                  exact False.elim (lt_asymm hlt hh)
              · exact hm
            refine ⟨ha,?_⟩
            obtain ⟨x,hx,_⟩ := hne
            let s := min x (f x)
            let t := max x (f x)
            have hs : s ∈ Ioo a b := ⟨lt_min hx.1 (hmap hx).1,(min_le_left _ _).trans_lt hx.2⟩
            have ht : t ∈ Ioo a b := ⟨hx.1.trans_le (le_max_left _ _),max_lt hx.2 (hmap hx).2⟩
            have hst : s ≤ t := min_le_max
            have hsub : Icc s t ⊆ Ioo a b := fun z hz => ⟨hs.1.trans_le hz.1,hz.2.trans_lt ht.2⟩
            have hfs : 0 ≤ f s - s := by
              rcases le_total x (f x) with hh | hh
              · simp only [s,min_eq_left hh]; linarith
              · simp only [s,min_eq_right hh,hinv x hx]; linarith
            have hft : f t - t ≤ 0 := by
              rcases le_total x (f x) with hh | hh
              · simp only [t,max_eq_right hh,hinv x hx]; linarith
              · simp only [t,max_eq_left hh]; linarith
            obtain ⟨z,hz,he⟩ := intermediate_value_Icc' hst ((hf.mono hsub).sub continuousOn_id) ⟨hft,hfs⟩
            have hfix : f z = z := sub_eq_zero.mp he
            refine ⟨z,⟨hsub hz,hfix⟩,?_⟩
            rintro y ⟨hy,hfy⟩
            rcases lt_trichotomy y z with hh | hh | hh
            · have hh' := ha hy (hsub hz) hh
              rw [hfy,hfix] at hh'
              exact False.elim (lt_asymm hh hh')
            · exact hh
            · have hh' := ha (hsub hz) hy hh
              rw [hfy,hfix] at hh'
              exact False.elim (lt_asymm hh hh')
      
          obtain ⟨f,hf,hmap,hfi,hproj,hfn⟩ := hChart j hinv hneg hne
          obtain ⟨ha,q,⟨hq,hfq⟩,hqunique⟩ := hInterval (-Real.pi) Real.pi
            (by linarith [Real.pi_pos]) f hf hmap hfi hfn
          have hnegarg : Complex.arg ((-1 : Circle) : ℂ) = Real.pi := by simp
          have harg {z : Circle} (hz : z ≠ -1) : Complex.arg (z : ℂ) ∈ Ioo (-Real.pi) Real.pi := by
            refine ⟨Complex.neg_pi_lt_arg _,lt_of_le_of_ne (Complex.arg_le_pi _) ?_⟩
            intro he
            exact hz (Circle.injective_arg (he.trans hnegarg.symm))
          have hqne : Circle.exp q ≠ -1 := by
            intro he
            have hh := congrArg (fun z : Circle => Complex.arg (z : ℂ)) he
            rw [Circle.arg_exp hq.1 hq.2.le,hnegarg] at hh
            exact (ne_of_lt hq.2) hh
          have hjq : j (Circle.exp q) = Circle.exp q := by
            rw [← hproj q hq,hfq]
          refine ⟨Circle.exp q,hqne,hjq,?_⟩
          intro z
          constructor
          · intro hzfix
            by_cases hz : z = -1
            · exact Or.inl hz
            · right
              have hzx := harg hz
              have hfz : f (Complex.arg (z : ℂ)) = Complex.arg (z : ℂ) := by
                have hh := congrArg (fun w : Circle => Complex.arg (w : ℂ)) (hproj _ hzx)
                rw [Circle.arg_exp (hmap hzx).1 (hmap hzx).2.le,Circle.exp_arg,hzfix] at hh
                exact hh
              have hxq := hqunique _ ⟨hzx,hfz⟩
              rw [← Circle.exp_arg z,hxq]
          · rintro (rfl | rfl)
            · exact hneg
            · exact hjq
    
      let r : Circle ≃ₜ Circle := Homeomorph.mulLeft ((-1 : Circle) * p⁻¹)
      have hrp : r p = -1 := by simp [r,mul_assoc]
      have hrs : r.symm (-1) = p := by rw [← hrp,r.symm_apply_apply]
      let k : Circle ≃ₜ Circle := r.symm.trans (j.trans r)
      have hk (z) : k z = r (j (r.symm z)) := rfl
      have hki : Function.Involutive k := by
        intro z
        rw [hk,hk,r.symm_apply_apply,hinv,r.apply_symm_apply]
      have hkn : k (-1) = -1 := by rw [hk,hrs,hp,hrp]
      have hkne : ∃ z, k z ≠ z := by
        obtain ⟨z,hz⟩ := hne
        refine ⟨r z,?_⟩
        intro he
        rw [hk,r.symm_apply_apply] at he
        exact hz (r.injective he)
      obtain ⟨q,hq,hkq,hclass⟩ := hNeg k hki hkn hkne
      have hqp : r.symm q ≠ p := by
        intro he
        have hh := congrArg r he
        rw [r.apply_symm_apply,hrp] at hh
        exact hq hh
      have hjq : j (r.symm q) = r.symm q := by
        apply r.injective
        exact hkq.trans (r.apply_symm_apply q).symm
      refine ⟨r.symm q,hqp,hjq,?_⟩
      intro z
      constructor
      · intro hz
        have hkr : k (r z) = r z := by rw [hk,r.symm_apply_apply,hz]
        rcases (hclass (r z)).mp hkr with he | he
        · exact Or.inl (r.injective (he.trans hrp.symm))
        · exact Or.inr (r.eq_symm_apply.mpr he)
      · rintro (rfl | rfl)
        · exact hp
        · exact hjq
  
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
  
  obtain ⟨j,hj,hi,hfix,hne⟩ := hInvolution c hc
  obtain ⟨p,hp⟩ := hbranch
  have hjp : j p = p := (hfix p).mpr hp
  obtain ⟨q,hqp,hjq,hclass⟩ := hClassify j hi hne p hjp
  have hpq : p ≠ q := hqp.symm
  let P := Circle.path p q
  have hPi : Function.Injective P := Circle.path_injective_of_ne hpq
  have hpair : j '' ({p,q}:Set Circle) = {p,q} := by
    simp only [Set.image_insert_eq,Set.image_singleton,hjp,hjq]
  have hno (t : unitInterval) (ht : t ∈ Ioo 0 1) : j (P t) ≠ P t := by
    intro he
    rcases (hclass (P t)).mp he with he | he
    · have ht0 : t = 0 := hPi (he.trans P.source.symm)
      exact (ne_of_gt ht.1) ht0
    · have ht1 : t = 1 := hPi (he.trans P.target.symm)
      exact (ne_of_lt ht.2) ht1
  obtain ⟨hex,hcover,hinter⟩ := hExchange p q hpq j hi hpair hno
  let α : Interval → S := fun t => M.cover.projection (c.map (P t))
  have hαi : Function.Injective α := by
    intro s t he
    rcases (M.cover.fiber_pair (c.map (P s)) (c.map (P t))).mp he with he | he
    · exact (hPi (c.embedded.injective he)).symm
    · have hJ : P t = j (P s) := c.embedded.injective (he.trans (hj (P s)).symm)
      have hpT : P t ∈ Set.range P ∩ j '' Set.range P :=
        ⟨⟨t,rfl⟩,⟨P s,⟨s,rfl⟩,hJ.symm⟩⟩
      rw [hinter] at hpT
      have hTf : j (P t) = P t := by
        rcases hpT with hT | hT
        · rw [hT,hjp]
        · rw [hT,hjq]
      have hST : P s = P t := by
        calc P s = j (j (P s)) := (hi (P s)).symm
             _ = j (P t) := congrArg j hJ.symm
             _ = P t := hTf
      exact hPi hST
  let arc : MarkedArc M :=
    { map := α
      continuous := M.cover.projection_continuous.comp (c.embedded.continuous.comp P.continuous)
      injective_except_loop_closure := fun s t he => Or.inl (hαi he)
      start_marked := by
        change M.cover.projection (c.map (P 0)) ∈ M.cover.branch
        rw [P.source]
        exact hp
      end_marked := by
        change M.cover.projection (c.map (P 1)) ∈ M.cover.branch
        rw [P.target]
        exact (hfix q).mp hjq
      marked_only_at_ends := by
        intro t ht
        rcases (hclass (P t)).mp ((hfix (P t)).mpr ht) with he | he
        · exact Or.inl (hPi (he.trans P.source.symm))
        · exact Or.inr (hPi (he.trans P.target.symm)) }
  have hends : arc.map 0 ≠ arc.map 1 := by
    intro he
    have ht := hαi he
    exact (by norm_num : (0:Interval) ≠ 1) ht
  let a : NonLoopArc M := ⟨arc,hends⟩
  have hαimage : Set.range α = M.cover.projection '' c.image := by
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
  refine ⟨a,?_⟩
  change c.image = M.cover.projection ⁻¹' Set.range α
  rw [hαimage]
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
