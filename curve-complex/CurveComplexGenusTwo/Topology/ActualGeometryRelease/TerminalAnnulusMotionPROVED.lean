import CurveComplexGenusTwo.Foundations.Definitions
open Set Topology CurveComplex
namespace CurveComplex.G3Review
variable {E : Type} [TopologicalSpace E]
theorem actual_circle_band_ambient_motion :
      ∃ K : AmbientIsotopy (Circle × Interval), ∃ J : C(Interval × (Circle × Interval),Circle × Interval),
        (∀ t z, J (t,K.map (t,z)) = z) ∧
        (∀ t z, K.map (t,J (t,z)) = z) ∧
        (∀ t z, K.map (t,(z,0)) = (z,0)) ∧
        (∀ t z, K.map (t,(z,1)) = (z,1)) ∧
        (∀ z, K.finalMap (z,⟨1/3,by norm_num⟩) = (z,⟨2/3,by norm_num⟩)) := by
    let r (t u : Interval) : ℝ :=
      if (u : ℝ) ≤ 1/3 then (1 + (t : ℝ)) * u
      else (1 - (t : ℝ)/2) * u + (t : ℝ)/2
    let v (t u : Interval) : ℝ :=
      if (u : ℝ) ≤ (1 + (t : ℝ))/3 then (u : ℝ)/(1 + (t : ℝ))
      else ((u : ℝ) - (t : ℝ)/2)/(1 - (t : ℝ)/2)
    have ha (t : Interval) : 0 < 1 + (t : ℝ) := by linarith [t.property.1]
    have hb (t : Interval) : 0 < 1 - (t : ℝ)/2 := by linarith [t.property.2]
    have htwo (t : Interval) : (2 : ℝ) - (t : ℝ) ≠ 0 := by linarith [t.property.2]
    have hrmem (t u : Interval) : r t u ∈ Set.Icc (0:ℝ) 1 := by
      dsimp [r]
      split_ifs with h
      · constructor <;> nlinarith [t.property.1,t.property.2,u.property.1]
      · constructor <;> nlinarith [t.property.1,t.property.2,u.property.1,u.property.2]
    have hvmem (t u : Interval) : v t u ∈ Set.Icc (0:ℝ) 1 := by
      dsimp [v]
      split_ifs with h
      · constructor
        · exact div_nonneg u.property.1 (ha t).le
        · apply (div_le_iff₀ (ha t)).mpr
          nlinarith [u.property.2,t.property.1]
      · constructor
        · apply (le_div_iff₀ (hb t)).mpr
          nlinarith [t.property.1,t.property.2]
        · apply (div_le_iff₀ (hb t)).mpr
          linarith [u.property.2]
    let R (t u : Interval) : Interval := ⟨r t u,hrmem t u⟩
    let V (t u : Interval) : Interval := ⟨v t u,hvmem t u⟩
    have hRc : Continuous (fun tu : Interval × Interval => R tu.1 tu.2) := by
      apply Continuous.subtype_mk
      apply continuous_if_le (by fun_prop) continuous_const
        (by fun_prop) (by fun_prop)
      intro tu htu
      rw [htu]
      ring
    have hVc : Continuous (fun tu : Interval × Interval => V tu.1 tu.2) := by
      apply Continuous.subtype_mk
      apply continuous_if_le (by fun_prop) (by fun_prop)
        (by exact (continuous_snd.subtype_val.div (continuous_const.add
          continuous_fst.subtype_val) (fun tu => (ha tu.1).ne')).continuousOn)
        (by exact ((continuous_snd.subtype_val.sub
          (continuous_fst.subtype_val.div_const 2)).div
          (continuous_const.sub (continuous_fst.subtype_val.div_const 2))
          (fun tu => (hb tu.1).ne')).continuousOn)
      intro tu htu
      have h1 := ha tu.1
      have h2 := hb tu.1
      rw [htu]
      field_simp [(ha tu.1).ne', (hb tu.1).ne', htwo tu.1]
      ring
    have hVR (t u : Interval) : V t (R t u) = u := by
      apply Subtype.ext
      dsimp [V,R,v,r]
      split_ifs with hu hv hv
      · field_simp [(ha t).ne', (hb t).ne', htwo t] <;> ring
      · exfalso
        nlinarith [t.property.1]
      · exfalso
        nlinarith [t.property.2]
      · field_simp [(ha t).ne', (hb t).ne', htwo t] <;> ring
    have hRV (t u : Interval) : R t (V t u) = u := by
      apply Subtype.ext
      dsimp [V,R,v,r]
      split_ifs with hu hv hv
      · field_simp [(ha t).ne', (hb t).ne', htwo t] <;> ring
      · exfalso
        have hh : (u : ℝ)/(1+(t:ℝ)) ≤ 1/3 :=
          (div_le_iff₀ (ha t)).mpr (by linarith)
        exact hv hh
      · exfalso
        have hh := (div_le_iff₀ (hb t)).mp hv
        linarith
      · field_simp [(ha t).ne', (hb t).ne', htwo t] <;> ring
    let map : C(Interval × (Circle × Interval),Circle × Interval) :=
      ⟨fun z => (z.2.1,R z.1 z.2.2),continuous_snd.fst.prodMk
        (hRc.comp (continuous_fst.prodMk continuous_snd.snd))⟩
    let invmap : C(Interval × (Circle × Interval),Circle × Interval) :=
      ⟨fun z => (z.2.1,V z.1 z.2.2),continuous_snd.fst.prodMk
        (hVc.comp (continuous_fst.prodMk continuous_snd.snd))⟩
    have hR0 (u : Interval) : R 0 u = u := by
      apply Subtype.ext
      dsimp [R,r]
      split_ifs <;> simp
    let K : AmbientIsotopy (Circle × Interval) := {
      map := map
      homeomorphism_at := by
        intro t
        refine ⟨{ toFun := fun z => (z.1,R t z.2)
                  invFun := fun z => (z.1,V t z.2)
                  left_inv := fun z => Prod.ext rfl (hVR t z.2)
                  right_inv := fun z => Prod.ext rfl (hRV t z.2)
                  continuous_toFun := continuous_fst.prodMk
                    (hRc.comp (continuous_const.prodMk continuous_snd))
                  continuous_invFun := continuous_fst.prodMk
                    (hVc.comp (continuous_const.prodMk continuous_snd)) },fun z => rfl⟩
      at_zero := fun z => Prod.ext rfl (hR0 z.2) }
    refine ⟨K,invmap,fun t z => Prod.ext rfl (hVR t z.2),
      fun t z => Prod.ext rfl (hRV t z.2),?_,?_,?_⟩
    · intro t z
      apply Prod.ext
      · rfl
      apply Subtype.ext
      dsimp [K,map,R,r]
      simp
    · intro t z
      apply Prod.ext
      · rfl
      apply Subtype.ext
      dsimp [K,map,R,r]
      norm_num
    · intro z
      apply Prod.ext
      · rfl
      apply Subtype.ext
      dsimp [AmbientIsotopy.finalMap,K,map,R,r]
      norm_num


theorem actual_compact_embedded_motion_extension
      {Y X : Type} [TopologicalSpace Y] [CompactSpace Y]
      [TopologicalSpace X] [T2Space X]
      (B : Y → X) (hB : IsEmbedding B) (U : Set X) (hU : IsOpen U)
      (hUA : U ⊆ Set.range B) (K : AmbientIsotopy Y)
      (J : C(Interval × Y,Y))
      (hleft : ∀ t y, J (t,K.map (t,y)) = y)
      (hright : ∀ t y, K.map (t,J (t,y)) = y)
      (hfix : ∀ t y, B y ∉ U → K.map (t,y) = y) :
      ∃ H : AmbientIsotopy X, ∃ V : C(Interval × X,X),
        (∀ t y, H.map (t,B y) = B (K.map (t,y))) ∧
        (∀ t x, x ∉ U → H.map (t,x) = x) ∧
        (∀ t x, V (t,H.map (t,x)) = x) ∧
        (∀ t x, H.map (t,V (t,x)) = x) := by
    classical
    let A := Set.range B
    let e : Y ≃ₜ A := hB.toHomeomorph
    have he (x : X) (hx : x ∈ A) : B (e.symm ⟨x,hx⟩) = x :=
      congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
    let f (tx : Interval × X) : X :=
      if hx : tx.2 ∈ A then B (K.map (tx.1,e.symm ⟨tx.2,hx⟩)) else tx.2
    let v (tx : Interval × X) : X :=
      if hx : tx.2 ∈ A then B (J (tx.1,e.symm ⟨tx.2,hx⟩)) else tx.2
    have hfB (t : Interval) (y : Y) : f (t,B y) = B (K.map (t,y)) := by
      dsimp [f]
      rw [dite_eq_left (Set.mem_range_self y)]
      congr 2
      exact Prod.ext rfl (hB.toHomeomorph_symm_apply y)
    have hvB (t : Interval) (y : Y) : v (t,B y) = B (J (t,y)) := by
      dsimp [v]
      rw [dite_eq_left (Set.mem_range_self y)]
      congr 2
      exact Prod.ext rfl (hB.toHomeomorph_symm_apply y)
    have hJfix (t : Interval) (y : Y) (hy : B y ∉ U) : J (t,y) = y := by
      have hh := hleft t y
      rwa [hfix t y hy] at hh
    have hfid (t : Interval) (x : X) (hx : x ∉ U) : f (t,x) = x := by
      dsimp [f]
      split_ifs with hxA
      · rw [hfix t _ (by rwa [he x hxA]),he]
      · rfl
    have hvid (t : Interval) (x : X) (hx : x ∉ U) : v (t,x) = x := by
      dsimp [v]
      split_ifs with hxA
      · rw [hJfix t _ (by rwa [he x hxA]),he]
      · rfl
    have hA : IsClosed A := by simpa [A] using (isCompact_univ.image hB.continuous).isClosed
    have hunion : ((Prod.snd ⁻¹' A : Set (Interval × X)) ∪ Prod.snd ⁻¹' Uᶜ) = Set.univ := by
      ext tx
      simp only [Set.mem_union,Set.mem_preimage,Set.mem_compl_iff,Set.mem_univ,iff_true]
      by_cases hx : tx.2 ∈ U
      · exact Or.inl (hUA hx)
      · exact Or.inr hx
    have hfcont : Continuous f := by
      have hfirst : ContinuousOn f (Prod.snd ⁻¹' A) := by
        apply continuousOn_iff_continuous_domRestrict.mpr
        let lift : (Prod.snd ⁻¹' A : Set (Interval × X)) → Interval × Y :=
          fun z => (z.val.1,e.symm ⟨z.val.2,z.property⟩)
        have hlift : Continuous lift := continuous_subtype_val.fst.prodMk
          (e.symm.continuous.comp
            (continuous_subtype_val.snd.subtype_mk (fun z => z.property)))
        have hc := hB.continuous.comp (K.map.continuous.comp hlift)
        exact hc.congr (fun z => by
          change B (K.map (lift z)) = f z.val
          dsimp [f]
          have hz : z.val.2 ∈ A := z.property
          rw [dite_eq_left hz])
      have hsecond : ContinuousOn f (Prod.snd ⁻¹' Uᶜ) := by
        apply continuous_snd.continuousOn.congr
        intro tx hx
        exact hfid tx.1 tx.2 hx
      rw [← continuousOn_univ,← hunion]
      exact hfirst.union_of_isClosed hsecond (hA.preimage continuous_snd)
        (hU.isClosed_compl.preimage continuous_snd)
    have hvcont : Continuous v := by
      have hfirst : ContinuousOn v (Prod.snd ⁻¹' A) := by
        apply continuousOn_iff_continuous_domRestrict.mpr
        let lift : (Prod.snd ⁻¹' A : Set (Interval × X)) → Interval × Y :=
          fun z => (z.val.1,e.symm ⟨z.val.2,z.property⟩)
        have hlift : Continuous lift := continuous_subtype_val.fst.prodMk
          (e.symm.continuous.comp
            (continuous_subtype_val.snd.subtype_mk (fun z => z.property)))
        have hc := hB.continuous.comp (J.continuous.comp hlift)
        exact hc.congr (fun z => by
          change B (J (lift z)) = v z.val
          dsimp [v]
          have hz : z.val.2 ∈ A := z.property
          rw [dite_eq_left hz])
      have hsecond : ContinuousOn v (Prod.snd ⁻¹' Uᶜ) := by
        apply continuous_snd.continuousOn.congr
        intro tx hx
        exact hvid tx.1 tx.2 hx
      rw [← continuousOn_univ,← hunion]
      exact hfirst.union_of_isClosed hsecond (hA.preimage continuous_snd)
        (hU.isClosed_compl.preimage continuous_snd)
    have hvl (t : Interval) (x : X) : v (t,f (t,x)) = x := by
      by_cases hx : x ∈ A
      · obtain ⟨y,rfl⟩ := hx
        rw [hfB,hvB,hleft]
      · have hxU : x ∉ U := fun h => hx (hUA h)
        rw [hfid t x hxU,hvid t x hxU]
    have hfr (t : Interval) (x : X) : f (t,v (t,x)) = x := by
      by_cases hx : x ∈ A
      · obtain ⟨y,rfl⟩ := hx
        rw [hvB,hfB,hright]
      · have hxU : x ∉ U := fun h => hx (hUA h)
        rw [hvid t x hxU,hfid t x hxU]
    let H : AmbientIsotopy X := {
      map := ⟨f,hfcont⟩
      homeomorphism_at := by
        intro t
        refine ⟨{ toFun := fun x => f (t,x)
                  invFun := fun x => v (t,x)
                  left_inv := hvl t
                  right_inv := hfr t
                  continuous_toFun := hfcont.comp (continuous_const.prodMk continuous_id)
                  continuous_invFun := hvcont.comp (continuous_const.prodMk continuous_id) },fun x => rfl⟩
      at_zero := by
        intro x
        change f (0,x) = x
        by_cases hx : x ∈ A
        · obtain ⟨y,rfl⟩ := hx
          rw [hfB]
          exact congrArg B (K.at_zero y)
        · exact hfid 0 x (fun h => hx (hUA h)) }
    exact ⟨H,⟨v,hvcont⟩,hfB,hfid,hvl,hfr⟩


theorem actual_collared_annulus_ambient_alignment
      [T2Space E] (c d : Curve E) (B : Circle × Interval → E)
      (hB : IsEmbedding B)
      (hc : Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩)) = c.image)
      (hd : Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩)) = d.image)
      (hopen : IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1))) :
      ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
        H.finalMap '' c.image = d.image ∧
        (∀ t x, x ∉ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) → H.map (t,x) = x) ∧
        (∀ t x, J (t,H.map (t,x)) = x) ∧
        (∀ t x, H.map (t,J (t,x)) = x) := by
    obtain ⟨K,V,hleft,hright,hzero,hone,hfinal⟩ := actual_circle_band_ambient_motion
    let U := B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
    have hfix (t : Interval) (y : Circle × Interval) (hy : B y ∉ U) : K.map (t,y) = y := by
      by_cases hy0 : y.2 = 0
      · rw [show y = (y.1,0) from Prod.ext rfl hy0]
        exact hzero t y.1
      by_cases hy1 : y.2 = 1
      · rw [show y = (y.1,1) from Prod.ext rfl hy1]
        exact hone t y.1
      have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
      have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
      exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
    obtain ⟨H,J,hH,houtside,hJleft,hJright⟩ :=
      actual_compact_embedded_motion_extension B hB U hopen
        (Set.image_subset_range _ _) K V hleft hright hfix
    refine ⟨H,J,?_,houtside,hJleft,hJright⟩
    have hlevels (z : Circle) : H.finalMap (B (z,⟨1/3,by norm_num⟩)) =
        B (z,⟨2/3,by norm_num⟩) := by
      change H.map (1,B (z,⟨1/3,by norm_num⟩)) = _
      rw [hH]
      exact congrArg B (hfinal z)
    rw [← hc,← hd,← Set.range_comp]
    exact congrArg Set.range (funext hlevels)


end CurveComplex.G3Review
