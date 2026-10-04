import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualIntervalTwoLevelCalibrationLocal

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 3000000

-- Reuse of the reviewed G3 motion on TWO actual halves of one supplied annulus.
example (M : HyperellipticModel E S) (U : Set E)
    (T : Circle × Interval ≃ₜ U) (δ : ℝ) (hδ : 0 < δ) (hδq : δ < 1/4) :
    ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
      H.finalMap ''
        (Set.range (fun z : Circle => (T (z,⟨1/4,by norm_num⟩)).val) ∪
          Set.range (fun z : Circle => (T (z,⟨3/4,by norm_num⟩)).val)) =
        Set.range (fun z : Circle => (T (z,⟨1/2-δ,by constructor <;> linarith⟩)).val) ∪
          Set.range (fun z : Circle => (T (z,⟨1/2+δ,by constructor <;> linarith⟩)).val) ∧
      (∀ t z, H.map (t,(T (z,⟨1/2,by norm_num⟩)).val) =
        (T (z,⟨1/2,by norm_num⟩)).val) ∧
      (∀ t x, x ∉ U → H.map (t,x) = x) ∧
      (∀ t x, J (t,H.map (t,x)) = x) ∧
      (∀ t x, H.map (t,J (t,x)) = x) := by
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
    have hCalibration (b : ℝ) (hb0 : 1/2 < b) (hb1 : b < 1) :
        ∃ h : Interval ≃ₜ Interval,
          h 0 = 0 ∧ h 1 = 1 ∧
          h ⟨1/3,by norm_num⟩ = ⟨1/2,by norm_num⟩ ∧
          (h ⟨2/3,by norm_num⟩ : ℝ) = b := by
      audit_main14_base3
        let f : Interval → ℝ := fun u =>
          if (u:ℝ) ≤ 1/3 then 3*(u:ℝ)/2
          else if (u:ℝ) ≤ 2/3 then 1/2+3*(b-1/2)*((u:ℝ)-1/3)
          else b+3*(1-b)*((u:ℝ)-2/3)
        have hfmem (u : Interval) : f u ∈ Set.Icc (0:ℝ) 1 := by
          dsimp [f]
          split_ifs <;> constructor <;> nlinarith [u.property.1,u.property.2]
        have hc2 : Continuous (fun u : Interval =>
            if (u:ℝ) ≤ 2/3 then 1/2+3*(b-1/2)*((u:ℝ)-1/3)
            else b+3*(1-b)*((u:ℝ)-2/3)) := by
          apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) (by fun_prop)
          intro u hu
          rw [hu]
          ring
        have hfc : Continuous f := by
          apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) hc2.continuousOn
          intro u hu
          rw [hu,if_pos (by norm_num : (1/3:ℝ) ≤ 2/3)]
          ring
        have hmono : StrictMono f := by
          intro x y hxy
          have hxyR : (x:ℝ) < (y:ℝ) := hxy
          have hcentral : 0 < 3*(b-1/2)*((y:ℝ)-(x:ℝ)) :=
            mul_pos (mul_pos (by norm_num) (sub_pos.mpr hb0)) (sub_pos.mpr hxyR)
          have houter : 0 < 3*(1-b)*((y:ℝ)-(x:ℝ)) :=
            mul_pos (mul_pos (by norm_num) (sub_pos.mpr hb1)) (sub_pos.mpr hxyR)
          dsimp [f]
          split_ifs <;> nlinarith [x.property.1,x.property.2,y.property.1,y.property.2]
        let F : Interval → Interval := fun u => ⟨f u,hfmem u⟩
        have hFc : Continuous F := hfc.subtype_mk _
        have hF0 : F 0 = 0 := Subtype.ext (by norm_num [F,f])
        have hF1 : F 1 = 1 := Subtype.ext (by norm_num [F,f]; ring)
        have hFs : Function.Surjective F := by
          have hconn := (isConnected_range hFc).isPreconnected.ordConnected
          intro u
          exact hconn.out ⟨0,hF0⟩ ⟨1,hF1⟩ u.property
        have hFi : Function.Injective F := by
          intro x y hxy
          exact hmono.injective (congrArg Subtype.val hxy)
        let h : Interval ≃ₜ Interval :=
          (Equiv.ofBijective F ⟨hFi,hFs⟩).toHomeomorphOfContinuousClosed hFc hFc.isClosedMap
        refine ⟨h,hF0,hF1,?_,?_⟩
        · apply Subtype.ext
          change f ⟨1/3,by norm_num⟩ = 1/2
          norm_num [f]
        · change f ⟨2/3,by norm_num⟩ = b
          norm_num [f]
          ring
    obtain ⟨k,hk0,hk1,hkthird,hktwo⟩ := hCalibration (1-2*δ) (by linarith) (by linarith)
    have hkInterior (u : Interval) (hu : u ∈ Set.Ioo (0:Interval) 1) : k u ∈ Set.Ioo (0:Interval) 1 := by
      constructor
      · apply lt_of_le_of_ne (k u).property.1
        intro he
        have heI : k u = 0 := Subtype.ext he.symm
        have hh := k.injective (heI.trans hk0.symm)
        subst u
        exact (lt_irrefl (0:Interval)) hu.1
      · apply lt_of_le_of_ne (k u).property.2
        intro he
        have heI : k u = 1 := Subtype.ext he
        have hh := k.injective (heI.trans hk1.symm)
        subst u
        exact (lt_irrefl (1:Interval)) hu.2
    let L : Circle × Interval → E := fun p =>
      (T (p.1,⟨(k p.2 : ℝ)/2,by constructor <;> linarith [(k p.2).property.1,(k p.2).property.2]⟩)).val
    let R : Circle × Interval → E := fun p =>
      (T (p.1,⟨1-(k p.2 : ℝ)/2,by constructor <;> linarith [(k p.2).property.1,(k p.2).property.2]⟩)).val
    have hLc : Continuous L := by dsimp [L]; fun_prop
    have hRc : Continuous R := by dsimp [R]; fun_prop
    have hLi : Function.Injective L := by
      intro p q he
      have hh := T.injective (Subtype.ext he)
      apply Prod.ext
      · have hx := congrArg (fun x : Circle × Interval => x.1) hh
        exact hx
      · apply Subtype.ext
        have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
        change (k p.2 : ℝ)/2 = (k q.2 : ℝ)/2 at hc
        exact congrArg Subtype.val (k.injective (Subtype.ext (by linarith)))
    have hRi : Function.Injective R := by
      intro p q he
      have hh := T.injective (Subtype.ext he)
      apply Prod.ext
      · have hx := congrArg (fun x : Circle × Interval => x.1) hh
        exact hx
      · apply Subtype.ext
        have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
        change 1-(k p.2 : ℝ)/2 = 1-(k q.2 : ℝ)/2 at hc
        exact congrArg Subtype.val (k.injective (Subtype.ext (by linarith)))
    have hL : Topology.IsEmbedding L := (hLc.isClosedEmbedding hLi).isEmbedding
    have hR : Topology.IsEmbedding R := (hRc.isClosedEmbedding hRi).isEmbedding
    let UL := L '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
    let UR := R '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
    have hUL : IsOpen UL := actual_embedded_annulus_interior_isOpen L hL
    have hUR : IsOpen UR := actual_embedded_annulus_interior_isOpen R hR
    obtain ⟨K,V,hleft,hright,hzero,hone,hfinal⟩ := CurveComplex.G3Review.actual_circle_band_ambient_motion
    have hfixL (t : Interval) (y : Circle × Interval) (hy : L y ∉ UL) : K.map (t,y) = y := by
      by_cases hy0 : y.2 = 0
      · rw [show y = (y.1,0) from Prod.ext rfl hy0]
        exact hzero t y.1
      by_cases hy1 : y.2 = 1
      · rw [show y = (y.1,1) from Prod.ext rfl hy1]
        exact hone t y.1
      have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
      have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
      exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
    have hfixR (t : Interval) (y : Circle × Interval) (hy : R y ∉ UR) : K.map (t,y) = y := by
      by_cases hy0 : y.2 = 0
      · rw [show y = (y.1,0) from Prod.ext rfl hy0]
        exact hzero t y.1
      by_cases hy1 : y.2 = 1
      · rw [show y = (y.1,1) from Prod.ext rfl hy1]
        exact hone t y.1
      have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
      have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
      exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
    obtain ⟨HL,JL,hHL,hLout,hJLleft,hJLright⟩ :=
      CurveComplex.G3Review.actual_compact_embedded_motion_extension L hL UL hUL
        (Set.image_subset_range _ _) K V hleft hright hfixL
    obtain ⟨HR,JR,hHR,hRout,hJRleft,hJRright⟩ :=
      CurveComplex.G3Review.actual_compact_embedded_motion_extension R hR UR hUR
        (Set.image_subset_range _ _) K V hleft hright hfixR
    have hLow (z : Circle) (u : Interval) (hu : (u : ℝ) ≤ 1/2) : (T (z,u)).val ∉ UR := by
      rintro ⟨p,⟨_,hp⟩,he⟩
      have hh := T.injective (Subtype.ext he)
      have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
      change 1-(k p.2 : ℝ)/2 = (u : ℝ) at hc
      have hp1 : (k p.2 : ℝ) < 1 := (hkInterior p.2 hp).2
      linarith
    have hHigh (z : Circle) (u : Interval) (hu : 1/2 ≤ (u : ℝ)) : (T (z,u)).val ∉ UL := by
      rintro ⟨p,⟨_,hp⟩,he⟩
      have hh := T.injective (Subtype.ext he)
      have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
      change (k p.2 : ℝ)/2 = (u : ℝ) at hc
      have hp1 : (k p.2 : ℝ) < 1 := (hkInterior p.2 hp).2
      linarith
    let H : AmbientIsotopy E := {
      map := ⟨fun p => HR.map (p.1,HL.map (p.1,p.2)),HR.map.continuous.comp
        (continuous_fst.prodMk (HL.map.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨l,hl⟩ := HL.homeomorphism_at t
        obtain ⟨r,hr⟩ := HR.homeomorphism_at t
        exact ⟨l.trans r,fun x => by change r (l x) = HR.map (t,HL.map (t,x)); rw [hl,hr]⟩
      at_zero := by
        intro x
        change HR.map (⟨0,by norm_num⟩,HL.map (⟨0,by norm_num⟩,x)) = x
        rw [HL.at_zero,HR.at_zero] }
    let J : C(Interval × E,E) := ⟨fun p => JL (p.1,JR (p.1,p.2)),JL.continuous.comp
      (continuous_fst.prodMk (JR.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
    have hLf (z : Circle) : HL.finalMap (T (z,⟨1/4,by norm_num⟩)).val =
        (T (z,⟨1/2-δ,by constructor <;> linarith⟩)).val := by
      have h := hHL 1 (z,⟨1/3,by norm_num⟩)
      have hk := hfinal z
      change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
      rw [hk] at h
      norm_num [AmbientIsotopy.finalMap,L,hkthird,hktwo] at h ⊢
      have heq : (1-2*δ)/2 = 1/2-δ := by ring
      simpa only [heq] using h
    have hRf (z : Circle) : HR.finalMap (T (z,⟨3/4,by norm_num⟩)).val =
        (T (z,⟨1/2+δ,by constructor <;> linarith⟩)).val := by
      have h := hHR 1 (z,⟨1/3,by norm_num⟩)
      have hk := hfinal z
      change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
      rw [hk] at h
      norm_num [AmbientIsotopy.finalMap,R,hkthird,hktwo] at h ⊢
      have heq : 1-(1-2*δ)/2 = 1/2+δ := by ring
      simpa only [heq] using h
    have hHfL (z : Circle) : H.finalMap (T (z,⟨1/4,by norm_num⟩)).val =
        (T (z,⟨1/2-δ,by constructor <;> linarith⟩)).val := by
      change HR.finalMap (HL.finalMap _) = _
      rw [hLf]
      exact hRout 1 _ (hLow z _ (by change (1/2-δ:ℝ) ≤ 1/2; linarith))
    have hHfR (z : Circle) : H.finalMap (T (z,⟨3/4,by norm_num⟩)).val =
        (T (z,⟨1/2+δ,by constructor <;> linarith⟩)).val := by
      change HR.finalMap (HL.finalMap _) = _
      rw [show HL.finalMap (T (z,⟨3/4,by norm_num⟩)).val = (T (z,⟨3/4,by norm_num⟩)).val from
        hLout 1 _ (hHigh z _ (by change (1/2:ℝ) ≤ 3/4; norm_num))]
      exact hRf z
    refine ⟨H,J,?_,?_,?_,?_,?_⟩
    · rw [Set.image_union,← Set.range_comp,← Set.range_comp]
      exact congrArg₂ Set.union (congrArg Set.range (funext hHfL)) (congrArg Set.range (funext hHfR))
    · intro t z
      change HR.map (t,HL.map (t,_)) = _
      rw [hLout t _ (hHigh z _ (by norm_num)),hRout t _ (hLow z _ (by norm_num))]
    · intro t x hx
      have hxL : x ∉ UL := by
        rintro ⟨p,hp,rfl⟩
        exact hx (T _).property
      have hxR : x ∉ UR := by
        rintro ⟨p,hp,rfl⟩
        exact hx (T _).property
      change HR.map (t,HL.map (t,x)) = x
      rw [hLout t x hxL,hRout t x hxR]
    · intro t x
      change JL (t,JR (t,HR.map (t,HL.map (t,x)))) = x
      rw [hJRleft,hJLleft]
    · intro t x
      change HR.map (t,HL.map (t,JL (t,JR (t,x)))) = x
      rw [hJLright,hJRright]

end CurveComplex.HyperellipticModel
