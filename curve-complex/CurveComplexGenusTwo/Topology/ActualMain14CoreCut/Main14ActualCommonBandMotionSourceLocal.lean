import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualCoreAnnulusEndpointTransportLocal
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.TerminalAnnulusMotionPROVED
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 5000000

-- Actual common closed band and simultaneous TWO-component motion, from the original source data.
example (M : HyperellipticModel E S) (b : NonLoopArc M)
    (Nb : ArcNeighborhood b) (U : Set E)
    (T : Circle × Interval ≃ₜ U)
    (hTc : Set.range (fun z : Circle => (T (z,⟨1/2,by norm_num⟩)).val) =
      M.cover.projection ⁻¹' b.image) :
    ∃ W : Set E, ∃ A : Circle × Interval ≃ₜ W,
      W ⊆ U ∧ W ⊆ M.cover.projection ⁻¹' interior Nb.closedSet ∧
      Disjoint W (Set.range (fun z : Circle => (T (z,0)).val) ∪
        Set.range (fun z : Circle => (T (z,1)).val)) ∧
      Disjoint W (M.cover.projection ⁻¹' Nb.boundary.image) ∧
      Set.range (fun z : Circle => (A (z,⟨1/2,by norm_num⟩)).val) =
        M.cover.projection ⁻¹' b.image ∧
      ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
        H.finalMap ''
          (Set.range (fun z : Circle => (A (z,⟨1/6,by norm_num⟩)).val) ∪
            Set.range (fun z : Circle => (A (z,⟨5/6,by norm_num⟩)).val)) =
          Set.range (fun z : Circle => (A (z,⟨1/3,by norm_num⟩)).val) ∪
            Set.range (fun z : Circle => (A (z,⟨2/3,by norm_num⟩)).val) ∧
        (∀ t z, H.map (t,(A (z,⟨1/2,by norm_num⟩)).val) =
          (A (z,⟨1/2,by norm_num⟩)).val) ∧
        (∀ t x, x ∉ W → H.map (t,x) = x) ∧
        (∀ t x, J (t,H.map (t,x)) = x) ∧
        (∀ t x, H.map (t,J (t,x)) = x) := by
  audit_main14_base3
    have hMove (U : Set E) (T : Circle × Interval ≃ₜ U) : ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
          H.finalMap ''
            (Set.range (fun z : Circle => (T (z,⟨1/6,by norm_num⟩)).val) ∪
              Set.range (fun z : Circle => (T (z,⟨5/6,by norm_num⟩)).val)) =
            Set.range (fun z : Circle => (T (z,⟨1/3,by norm_num⟩)).val) ∪
              Set.range (fun z : Circle => (T (z,⟨2/3,by norm_num⟩)).val) ∧
          (∀ t z, H.map (t,(T (z,⟨1/2,by norm_num⟩)).val) =
            (T (z,⟨1/2,by norm_num⟩)).val) ∧
          (∀ t x, x ∉ U → H.map (t,x) = x) ∧
          (∀ t x, J (t,H.map (t,x)) = x) ∧
          (∀ t x, H.map (t,J (t,x)) = x) := by
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
      let L : Circle × Interval → E := fun p =>
        (T (p.1,⟨(p.2 : ℝ)/2,by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩)).val
      let R : Circle × Interval → E := fun p =>
        (T (p.1,⟨1-(p.2 : ℝ)/2,by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩)).val
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
          change (p.2 : ℝ)/2 = (q.2 : ℝ)/2 at hc
          linarith
      have hRi : Function.Injective R := by
        intro p q he
        have hh := T.injective (Subtype.ext he)
        apply Prod.ext
        · have hx := congrArg (fun x : Circle × Interval => x.1) hh
          exact hx
        · apply Subtype.ext
          have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
          change 1-(p.2 : ℝ)/2 = 1-(q.2 : ℝ)/2 at hc
          linarith
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
        change 1-(p.2 : ℝ)/2 = (u : ℝ) at hc
        have hp1 : (p.2 : ℝ) < 1 := hp.2
        linarith
      have hHigh (z : Circle) (u : Interval) (hu : 1/2 ≤ (u : ℝ)) : (T (z,u)).val ∉ UL := by
        rintro ⟨p,⟨_,hp⟩,he⟩
        have hh := T.injective (Subtype.ext he)
        have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
        change (p.2 : ℝ)/2 = (u : ℝ) at hc
        have hp1 : (p.2 : ℝ) < 1 := hp.2
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
      have hLf (z : Circle) : HL.finalMap (T (z,⟨1/6,by norm_num⟩)).val =
          (T (z,⟨1/3,by norm_num⟩)).val := by
        have h := hHL 1 (z,⟨1/3,by norm_num⟩)
        have hk := hfinal z
        change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
        rw [hk] at h
        norm_num [AmbientIsotopy.finalMap,L] at h ⊢
        exact h
      have hRf (z : Circle) : HR.finalMap (T (z,⟨5/6,by norm_num⟩)).val =
          (T (z,⟨2/3,by norm_num⟩)).val := by
        have h := hHR 1 (z,⟨1/3,by norm_num⟩)
        have hk := hfinal z
        change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
        rw [hk] at h
        norm_num [AmbientIsotopy.finalMap,R] at h ⊢
        exact h
      have hHfL (z : Circle) : H.finalMap (T (z,⟨1/6,by norm_num⟩)).val =
          (T (z,⟨1/3,by norm_num⟩)).val := by
        change HR.finalMap (HL.finalMap _) = _
        rw [hLf]
        exact hRout 1 _ (hLow z _ (by norm_num))
      have hHfR (z : Circle) : H.finalMap (T (z,⟨5/6,by norm_num⟩)).val =
          (T (z,⟨2/3,by norm_num⟩)).val := by
        change HR.finalMap (HL.finalMap _) = _
        rw [show HL.finalMap (T (z,⟨5/6,by norm_num⟩)).val = (T (z,⟨5/6,by norm_num⟩)).val from
          hLout 1 _ (hHigh z _ (by norm_num))]
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
    let c : Interval := ⟨1/2,by norm_num⟩
    let f : Circle × Interval → S := fun p => M.cover.projection (T p).val
    have hc : Continuous f := M.cover.projection_continuous.comp
      (continuous_subtype_val.comp T.continuous)
    have hopen : IsOpen (f ⁻¹' interior Nb.closedSet) := isOpen_interior.preimage hc
    have hmid : (Set.univ : Set Circle) ×ˢ {c} ⊆ f ⁻¹' interior Nb.closedSet := by
      rintro ⟨z,t⟩ ⟨_,ht⟩
      have he : t = c := ht
      subst t
      have hh : (T (z,c)).val ∈ M.cover.projection ⁻¹' b.image := by
        rw [← hTc]
        exact Set.mem_range_self z
      exact Nb.arc_inside hh
    obtain ⟨D,V,hD,hV,hall,hcV,hDV⟩ :=
      generalized_tube_lemma (isCompact_univ : IsCompact (Set.univ : Set Circle))
        (isCompact_singleton : IsCompact ({c} : Set Interval)) hopen hmid
    have hbandV (z : Circle) (t : Interval) (ht : t ∈ V) :
        M.cover.projection (T (z,t)).val ∈ interior Nb.closedSet :=
      hDV ⟨hall (Set.mem_univ z),ht⟩
    let clip : ℝ → Interval := Set.projIcc 0 1 (by norm_num)
    have hclip : Continuous clip := continuous_projIcc
    have hpre : IsOpen (clip ⁻¹' V) := hV.preimage hclip
    have hhalf : (1/2 : ℝ) ∈ clip ⁻¹' V := by
      have hcclip : clip (1/2) = c := by
        exact Set.projIcc_of_mem (by norm_num) (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
      change clip (1/2) ∈ V
      rw [hcclip]
      exact hcV (Set.mem_singleton c)
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hpre (1/2) hhalf
    let δ : ℝ := min (ε/2) (1/4)
    have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
    have hδsmall : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have hδquarter : δ ≤ 1/4 := min_le_right _ _
    let q : Interval → Interval := fun u =>
      ⟨1/2 + δ*(2*(u:ℝ)-1),by constructor <;> nlinarith [u.property.1,u.property.2]⟩
    have hqc : Continuous q := by dsimp [q]; fun_prop
    have hqi : Function.Injective q := by
      intro u v he
      apply Subtype.ext
      have hh := congrArg Subtype.val he
      change 1/2 + δ*(2*(u:ℝ)-1) = 1/2 + δ*(2*(v:ℝ)-1) at hh
      nlinarith
    have hqmid : q c = c := by apply Subtype.ext; dsimp [q,c]; ring
    have hqV (u : Interval) : q u ∈ V := by
      have hnear : (q u : ℝ) ∈ Metric.ball (1/2) ε := by
        rw [Metric.mem_ball,Real.dist_eq,abs_lt]
        dsimp [q]
        constructor <;> nlinarith [u.property.1,u.property.2]
      have hv := hball hnear
      change clip (q u : ℝ) ∈ V at hv
      rw [show clip (q u : ℝ) = q u from Set.projIcc_of_mem (by norm_num) (q u).property] at hv
      exact hv
    let B : Circle × Interval → E := fun p => (T (p.1,q p.2)).val
    have hBc : Continuous B := by dsimp [B]; fun_prop
    have hBi : Function.Injective B := by
      intro p w he
      have hh := T.injective (Subtype.ext he)
      apply Prod.ext
      · have hz := congrArg (fun x : Circle × Interval => x.1) hh
        exact hz
      · exact hqi (congrArg Prod.snd hh)
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    have hBe : Topology.IsEmbedding B := (hBc.isClosedEmbedding hBi).isEmbedding
    let W := Set.range B
    let A : Circle × Interval ≃ₜ W := hBe.toHomeomorph
    have hA (p : Circle × Interval) : (A p).val = (T (p.1,q p.2)).val := rfl
    refine ⟨W,A,?_,?_,?_,?_,?_,hMove W A⟩
    · rintro x ⟨p,rfl⟩
      exact (T _).property
    · rintro x ⟨p,rfl⟩
      exact hbandV p.1 (q p.2) (hqV p.2)
    · apply Set.disjoint_left.mpr
      rintro x ⟨p,rfl⟩ (⟨z,he⟩ | ⟨z,he⟩)
      · have hh := T.injective (Subtype.ext he)
        have hs := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
        change 0 = 1/2 + δ*(2*(p.2:ℝ)-1) at hs
        nlinarith [p.2.property.1,p.2.property.2]
      · have hh := T.injective (Subtype.ext he)
        have hs := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
        change 1 = 1/2 + δ*(2*(p.2:ℝ)-1) at hs
        nlinarith [p.2.property.1,p.2.property.2]
    · apply Set.disjoint_left.mpr
      rintro x ⟨p,rfl⟩ hx
      have hin := hbandV p.1 (q p.2) (hqV p.2)
      have hfront : M.cover.projection (B p) ∈ frontier Nb.closedSet := by
        rw [← Nb.boundary_eq_frontier]
        exact hx
      exact Set.disjoint_left.mp disjoint_interior_frontier hin hfront
    · have hh : (fun z : Circle => (A (z,c)).val) =
          (fun z : Circle => (T (z,c)).val) := by
        funext z
        rw [hA,hqmid]
      exact (congrArg Set.range hh).trans hTc

-- The actual common band is wholly in the INTERIOR of the second supplied annulus.
example (M : HyperellipticModel E S) (b : NonLoopArc M)
    (Nb : ArcNeighborhood b) (W : Set E)
    (A : Circle × Interval ≃ₜ W)
    (B : Circle × Interval ≃ₜ M.cover.projection ⁻¹' Nb.closedSet)
    (hWN : W ⊆ M.cover.projection ⁻¹' interior Nb.closedSet)
    (hAc : Set.range (fun z : Circle => (A (z,⟨1/2,by norm_num⟩)).val) =
      M.cover.projection ⁻¹' b.image)
    (hBc : Set.range (fun z : Circle => (B (z,⟨1/2,by norm_num⟩)).val) =
      M.cover.projection ⁻¹' b.image)
    (hBb : Set.range (fun z : Circle => (B (z,0)).val) ∪
      Set.range (fun z : Circle => (B (z,1)).val) =
      M.cover.projection ⁻¹' Nb.boundary.image) :
    ∃ G : C(Circle × Interval,Circle × Interval), Topology.IsEmbedding G ∧
      (∀ p, (B (G p)).val = (A p).val) ∧
      Set.range G ⊆ Set.univ ×ˢ Set.Ioo (0:Interval) 1 ∧
      ∃ r : Circle ≃ₜ Circle, ∀ z,
        G (z,⟨1/2,by norm_num⟩) = (r z,⟨1/2,by norm_num⟩) := by
  audit_main14_base3
    let f : Circle × Interval → M.cover.projection ⁻¹' Nb.closedSet := fun p =>
      ⟨(A p).val,(show M.cover.projection (A p).val ∈ Nb.closedSet from
        interior_subset (hWN (A p).property))⟩
    have hfc : Continuous f := (continuous_subtype_val.comp A.continuous).subtype_mk _
    let G : C(Circle × Interval,Circle × Interval) :=
      ⟨fun p => B.symm (f p),B.symm.continuous.comp hfc⟩
    have hfe : Topology.IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp hfc continuous_subtype_val
      change Topology.IsEmbedding (fun p : Circle × Interval => (A p).val)
      exact Topology.IsEmbedding.subtypeVal.comp A.isEmbedding
    have hG (p : Circle × Interval) : (B (G p)).val = (A p).val :=
      congrArg Subtype.val (B.apply_symm_apply (f p))
    have hnobound (p : Circle × Interval) : (G p).2 ≠ 0 ∧ (G p).2 ≠ 1 := by
      constructor
      · intro he
        have hx : (A p).val ∈ M.cover.projection ⁻¹' Nb.boundary.image := by
          rw [← hBb]
          apply Or.inl
          refine ⟨(G p).1,?_⟩
          have hh : ((G p).1,0) = G p := Prod.ext rfl he.symm
          change (B ((G p).1,0)).val = (A p).val
          rw [hh,hG]
        have hi := hWN (A p).property
        have hf : M.cover.projection (A p).val ∈ frontier Nb.closedSet := by
          rw [← Nb.boundary_eq_frontier]
          exact hx
        exact Set.disjoint_left.mp disjoint_interior_frontier hi hf
      · intro he
        have hx : (A p).val ∈ M.cover.projection ⁻¹' Nb.boundary.image := by
          rw [← hBb]
          apply Or.inr
          refine ⟨(G p).1,?_⟩
          have hh : ((G p).1,1) = G p := Prod.ext rfl he.symm
          change (B ((G p).1,1)).val = (A p).val
          rw [hh,hG]
        have hi := hWN (A p).property
        have hf : M.cover.projection (A p).val ∈ frontier Nb.closedSet := by
          rw [← Nb.boundary_eq_frontier]
          exact hx
        exact Set.disjoint_left.mp disjoint_interior_frontier hi hf
    refine ⟨G,B.symm.isEmbedding.comp hfe,hG,?_,?_⟩
    · rintro p ⟨x,rfl⟩
      exact ⟨Set.mem_univ _,lt_of_le_of_ne
        (show (0:Interval) ≤ (G x).2 from (G x).2.property.1) (hnobound x).1.symm,
        lt_of_le_of_ne (show (G x).2 ≤ (1:Interval) from (G x).2.property.2) (hnobound x).2⟩
    · let c : Interval := ⟨1/2,by norm_num⟩
      have hAe : Topology.IsEmbedding (fun z : Circle => (A (z,c)).val) :=
        Topology.IsEmbedding.subtypeVal.comp (A.isEmbedding.comp (isEmbedding_prodMkLeft c))
      have hBe : Topology.IsEmbedding (fun z : Circle => (B (z,c)).val) :=
        Topology.IsEmbedding.subtypeVal.comp (B.isEmbedding.comp (isEmbedding_prodMkLeft c))
      let ea : Circle ≃ₜ (M.cover.projection ⁻¹' b.image) :=
        hAe.toHomeomorph.trans (Homeomorph.setCongr hAc)
      let eb : Circle ≃ₜ (M.cover.projection ⁻¹' b.image) :=
        hBe.toHomeomorph.trans (Homeomorph.setCongr hBc)
      refine ⟨ea.trans eb.symm,?_⟩
      intro z
      apply B.injective
      apply Subtype.ext
      rw [hG]
      exact (congrArg Subtype.val (eb.apply_symm_apply (ea z))).symm

end CurveComplex.HyperellipticModel
