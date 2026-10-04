import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualCommonCoreTransitionSidesLocal

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 6000000

-- Actual two-annulus source: transition and opposite-side pairing are produced,
-- rather than assumed. Both parametrizations are the supplied original ones.
example (M : HyperellipticModel E S) (U V : Set E)
    (A : Circle × Interval ≃ₜ U) (B : Circle × Interval ≃ₜ V)
    (hsub : U ⊆ V)
    (hmid : Set.range (fun z : Circle => (A (z,⟨1/2,by norm_num⟩)).val) =
      Set.range (fun z : Circle => (B (z,⟨1/2,by norm_num⟩)).val)) :
    ∃ G : C(Circle × Interval,Circle × Interval), ∃ r : Circle ≃ₜ Circle,
      Topology.IsEmbedding G ∧
      (∀ p, (B (G p)).val = (A p).val) ∧
      (∀ z, G (z,⟨1/2,by norm_num⟩) = (r z,⟨1/2,by norm_num⟩)) ∧
      (((∀ z (u : Interval), (u:ℝ) < 1/2 → ((G (z,u)).2:ℝ) < 1/2) ∧
        (∀ z (u : Interval), 1/2 < (u:ℝ) → 1/2 < ((G (z,u)).2:ℝ))) ∨
      ((∀ z (u : Interval), (u:ℝ) < 1/2 → 1/2 < ((G (z,u)).2:ℝ)) ∧
        (∀ z (u : Interval), 1/2 < (u:ℝ) → ((G (z,u)).2:ℝ) < 1/2))) := by
  audit_main14_base3
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    have actual_embedded_annulus_interior_isOpen
        (B : Circle × Interval → E) (hB : IsEmbedding B) :
        IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
      rw [isOpen_iff_forall_mem_open]
      rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
      have hu0 : (0:ℝ) < (u : ℝ) := hu.1
      have hu1 : (u : ℝ) < 1 := hu.2
      let lo : ℝ := (u : ℝ)/2
      let hi : ℝ := ((u : ℝ)+1)/2
      have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
      have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
      have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
      have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
      have hlh : lo ≤ hi := (hlu.trans huh).le
      let width : ℝ → Interval := fun s =>
        ⟨(Set.projIcc lo hi hlh s : ℝ),
          ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
            le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
      have hwc : Continuous width :=
        (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
      let θ := Complex.arg (z : ℂ)
      let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
      have hfc : Continuous f := hB.continuous.comp
        ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
      let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
        {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
      have hΩ : IsOpen Ω :=
        (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
      have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
          (width (x 0) : ℝ) = x 0 :=
        congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
      have hfi : Set.InjOn f Ω := by
        intro x hx w hw he
        have hp := hB.injective he
        have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
          (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
          ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
        have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
        change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
        rw [hclip x hx,hclip w hw] at hwidth
        ext i
        fin_cases i
        · exact hwidth
        · exact hangle
      have hopen : IsOpen (f '' Ω) :=
        CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
      have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
        rintro q ⟨x,hx,rfl⟩
        refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
        · change 0 < (width (x 0) : ℝ)
          rw [hclip x hx]
          exact hl0.trans hx.1.1
        · change (width (x 0) : ℝ) < 1
          rw [hclip x hx]
          exact hx.1.2.trans hh1
      let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
      have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
      have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
      have hx : x ∈ Ω := by
        refine ⟨?_,?_⟩
        · rw [hx0]; exact ⟨hlu,huh⟩
        · rw [hx1]; constructor <;> linarith [Real.pi_pos]
      have hwu : width (u : ℝ) = u := by
        apply Subtype.ext
        change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
        exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
      have hpoint : f x = B (z,u) := by
        dsimp [f]
        rw [hx0,hx1,hwu,Circle.exp_arg]
      exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
    have hSides (G : C(Circle × Interval,Circle × Interval))
        (hG : Topology.IsEmbedding G) (r : Circle ≃ₜ Circle)
        (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩) = (r z,⟨1/2,by norm_num⟩))
        (hopen : IsOpen (G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1))) :
        ((∀ z (u : Interval), (u:ℝ) < 1/2 → ((G (z,u)).2:ℝ) < 1/2) ∧
          (∀ z (u : Interval), 1/2 < (u:ℝ) → 1/2 < ((G (z,u)).2:ℝ))) ∨
        ((∀ z (u : Interval), (u:ℝ) < 1/2 → 1/2 < ((G (z,u)).2:ℝ)) ∧
          (∀ z (u : Interval), 1/2 < (u:ℝ) → ((G (z,u)).2:ℝ) < 1/2)) := by
      audit_main14_base3
        let c : Interval := ⟨1/2,by norm_num⟩
        let L := G '' (Set.univ ×ˢ Set.Iio c)
        let R := G '' (Set.univ ×ˢ Set.Ioi c)
        let O := G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
        let Vlo : Set (Circle × Interval) := {p | p.2 < c}
        let Vhi : Set (Circle × Interval) := {p | c < p.2}
        have hLconn : IsPreconnected L := by
          letI : ConnectedSpace (Set.Ico (0:ℝ) (1/2)) :=
            Subtype.connectedSpace (isConnected_Ico (by norm_num : (0:ℝ) < 1/2))
          let f : Circle × Set.Ico (0:ℝ) (1/2) → Circle × Interval := fun p =>
            (p.1,⟨p.2.val,⟨p.2.property.1,p.2.property.2.le.trans (by norm_num)⟩⟩)
          have hf : Continuous f := by dsimp [f]; fun_prop
          have hr : Set.range (G ∘ f) = L := by
            ext p
            constructor
            · rintro ⟨⟨z,u⟩,rfl⟩
              exact ⟨f (z,u),⟨Set.mem_univ _,u.property.2⟩,rfl⟩
            · rintro ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩
              exact ⟨(z,⟨u.val,⟨u.property.1,hu⟩⟩),rfl⟩
          rw [← hr]
          exact (isConnected_range (G.continuous.comp hf)).isPreconnected
        have hRconn : IsPreconnected R := by
          letI : ConnectedSpace (Set.Ioc (1/2:ℝ) 1) :=
            Subtype.connectedSpace (isConnected_Ioc (by norm_num : (1/2:ℝ) < 1))
          let f : Circle × Set.Ioc (1/2:ℝ) 1 → Circle × Interval := fun p =>
            (p.1,⟨p.2.val,⟨(by norm_num : (0:ℝ) ≤ 1/2).trans p.2.property.1.le,p.2.property.2⟩⟩)
          have hf : Continuous f := by dsimp [f]; fun_prop
          have hr : Set.range (G ∘ f) = R := by
            ext p
            constructor
            · rintro ⟨⟨z,u⟩,rfl⟩
              exact ⟨f (z,u),⟨Set.mem_univ _,u.property.1⟩,rfl⟩
            · rintro ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩
              exact ⟨(z,⟨u.val,⟨hu,u.property.2⟩⟩),rfl⟩
          rw [← hr]
          exact (isConnected_range (G.continuous.comp hf)).isPreconnected
        have havoid (z : Circle) (u : Interval) (hu : u ≠ c) : (G (z,u)).2 ≠ c := by
          intro he
          let w := r.symm (G (z,u)).1
          have hg : G (w,c) = G (z,u) := by
            rw [hcore]
            exact Prod.ext (r.apply_symm_apply _) he.symm
          exact hu (congrArg Prod.snd (hG.injective hg)).symm
        have hsub (D : Set (Circle × Interval))
            (hD : ∀ p ∈ D, p.2 ≠ c) : D ⊆ Vlo ∪ Vhi := by
          intro p hp
          exact lt_or_gt_of_ne (hD p hp)
        have hdis : Disjoint Vlo Vhi := by
          apply Set.disjoint_left.mpr
          intro p hp hq
          change p.2 < c at hp
          change c < p.2 at hq
          exact lt_asymm hp hq
        have hld : L ⊆ Vlo ∨ L ⊆ Vhi :=
          IsPreconnected.subset_or_subset (isOpen_Iio.preimage continuous_snd)
            (isOpen_Ioi.preimage continuous_snd)
            hdis
            (hsub L (by rintro _ ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩; exact havoid z u hu.ne)) hLconn
        have hrd : R ⊆ Vlo ∨ R ⊆ Vhi :=
          IsPreconnected.subset_or_subset (isOpen_Iio.preimage continuous_snd)
            (isOpen_Ioi.preimage continuous_snd)
            hdis
            (hsub R (by rintro _ ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩; exact havoid z u hu.ne')) hRconn
        have hmid : (r 1,c) ∈ O := ⟨(1,c),⟨Set.mem_univ _,by change (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1; norm_num⟩,hcore 1⟩
        have hnotlo : ¬ (L ⊆ Vlo ∧ R ⊆ Vlo) := by
          rintro ⟨hl,hr⟩
          have hO : ∀ p ∈ O, p.2 ≤ c := by
            rintro _ ⟨⟨z,u⟩,hu,rfl⟩
            rcases lt_trichotomy u c with hh | hh | hh
            · exact (hl ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
            · rw [hh,hcore]
            · exact (hr ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
          have hc : (r 1,c) ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo c 1) := by
            rw [closure_prod_eq,closure_univ,closure_Ioo (show c ≠ 1 by intro hh; have hv := congrArg Subtype.val hh; norm_num [c] at hv)]
            exact ⟨Set.mem_univ _,le_rfl,by change (1/2:ℝ) ≤ 1; norm_num⟩
          obtain ⟨p,hpO,hp⟩ := mem_closure_iff.mp hc O hopen hmid
          exact not_lt_of_ge (hO p hpO) hp.2.1
        have hnothi : ¬ (L ⊆ Vhi ∧ R ⊆ Vhi) := by
          rintro ⟨hl,hr⟩
          have hO : ∀ p ∈ O, c ≤ p.2 := by
            rintro _ ⟨⟨z,u⟩,hu,rfl⟩
            rcases lt_trichotomy u c with hh | hh | hh
            · exact (hl ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
            · rw [hh,hcore]
            · exact (hr ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
          have hc : (r 1,c) ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo 0 c) := by
            rw [closure_prod_eq,closure_univ,closure_Ioo (show (0:Interval) ≠ c by intro hh; have hv := congrArg Subtype.val hh; norm_num [c] at hv)]
            exact ⟨Set.mem_univ _,by change (0:ℝ) ≤ 1/2; norm_num,le_rfl⟩
          obtain ⟨p,hpO,hp⟩ := mem_closure_iff.mp hc O hopen hmid
          exact not_lt_of_ge (hO p hpO) hp.2.2
        rcases hld with hl | hl <;> rcases hrd with hr | hr
        · exact False.elim (hnotlo ⟨hl,hr⟩)
        · exact Or.inl ⟨fun z u hu => hl ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩,
            fun z u hu => hr ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩⟩
        · exact Or.inr ⟨fun z u hu => hl ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩,
            fun z u hu => hr ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩⟩
        · exact False.elim (hnothi ⟨hl,hr⟩)
    let f : Circle × Interval → V := fun p => ⟨(A p).val,hsub (A p).property⟩
    have hfc : Continuous f := (continuous_subtype_val.comp A.continuous).subtype_mk _
    let G : C(Circle × Interval,Circle × Interval) :=
      ⟨fun p => B.symm (f p),B.symm.continuous.comp hfc⟩
    have hfe : Topology.IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp hfc continuous_subtype_val
      change Topology.IsEmbedding (fun p : Circle × Interval => (A p).val)
      exact Topology.IsEmbedding.subtypeVal.comp A.isEmbedding
    have hGe : Topology.IsEmbedding G := B.symm.isEmbedding.comp hfe
    have hG (p : Circle × Interval) : (B (G p)).val = (A p).val :=
      congrArg Subtype.val (B.apply_symm_apply (f p))
    let c : Interval := ⟨1/2,by norm_num⟩
    have hAe : Topology.IsEmbedding (fun z : Circle => (A (z,c)).val) :=
      Topology.IsEmbedding.subtypeVal.comp (A.isEmbedding.comp (isEmbedding_prodMkLeft c))
    have hBe : Topology.IsEmbedding (fun z : Circle => (B (z,c)).val) :=
      Topology.IsEmbedding.subtypeVal.comp (B.isEmbedding.comp (isEmbedding_prodMkLeft c))
    let C := Set.range (fun z : Circle => (A (z,c)).val)
    let ea : Circle ≃ₜ C := hAe.toHomeomorph
    let eb : Circle ≃ₜ C := hBe.toHomeomorph.trans (Homeomorph.setCongr hmid.symm)
    let r := ea.trans eb.symm
    have hcore (z : Circle) : G (z,c) = (r z,c) := by
      apply B.injective
      apply Subtype.ext
      rw [hG]
      exact (congrArg Subtype.val (eb.apply_symm_apply (ea z))).symm
    have hAo : IsOpen ((fun p : Circle × Interval => (A p).val) ''
        (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) :=
      actual_embedded_annulus_interior_isOpen _
        (Topology.IsEmbedding.subtypeVal.comp A.isEmbedding)
    have hEq : G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) =
        (fun p : Circle × Interval => (B p).val) ⁻¹'
          ((fun p : Circle × Interval => (A p).val) ''
            (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
      ext p
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨w,hw,(hG w).symm⟩
      · rintro ⟨w,hw,he⟩
        refine ⟨w,hw,?_⟩
        exact B.injective (Subtype.ext ((hG w).trans he))
    have hGo : IsOpen (G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
      rw [hEq]
      exact hAo.preimage (continuous_subtype_val.comp B.continuous)
    exact ⟨G,r,hGe,hG,hcore,hSides G hGe r hcore hGo⟩

end CurveComplex.HyperellipticModel
