import CurveComplexGenusTwo.Topology.Smoothing.ActualGermArcs
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
open Set Topology Schoenflies CurveComplex
open scoped Manifold
set_option maxHeartbeats 1600000
theorem finite_actual_interval_compatible_crosscut_charts {S : Type} [TopologicalSpace S] [T2Space S] [NormalSpace S]
    (K : Type) [Fintype K] (γ : K → Interval → S)
    (hγ : ∀ k, Continuous (γ k))
    (hcoll : ∀ k t u, γ k t = γ k u → t = u ∨
      (t = (0:Interval) ∧ u = (1:Interval)) ∨
      (t = (1:Interval) ∧ u = (0:Interval)))
    (a b : K → ℝ) (ha : ∀ k, 0 < a k) (hab : ∀ k, a k < b k)
    (hb : ∀ k, b k < 1)
    (e : K → OpenPartialHomeomorph S Plane)
    (hsub : ∀ k, (γ k ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (a k) (b k) ⊆ (e k).source)
    (hdis : ∀ i j, i ≠ j → Disjoint
      ((γ i ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (a i) (b i))
      ((γ j ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (a j) (b j))) :
    let g := fun k => γ k ∘ Set.projIcc 0 1 zero_le_one
    ∃ E : K → OpenPartialHomeomorph S Plane,
      (∀ k, (E k).source ⊆ (e k).source) ∧
      (∀ i j, i ≠ j → Disjoint (E i).source (E j).source) ∧
      (∀ k, Plane.closedSquare 0 1 ⊆ (E k).target) ∧
      (∀ k, g k '' Set.Icc (a k) (b k) ⊆ (E k).source) ∧
      (∀ k, E k (g k (a k)) = Plane.mk (-1) 0 ∧ E k (g k (b k)) = Plane.mk 1 0) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ Set.range (γ k) ↔ E k x 1 = 0)) ∧
      (∀ k, {x : S | x ∈ (E k).source ∧ E k x ∈ Plane.closedSquare 0 1} ∩
        Set.range (γ k) = g k '' Set.Icc (a k) (b k)) := by
  classical
  have hchart {S : Type} [TopologicalSpace S] [T2Space S]
      (γ : Interval → S) (hγ : Continuous γ)
      (hcoll : ∀ t u, γ t = γ u → t = u ∨
        (t = (0:Interval) ∧ u = (1:Interval)) ∨
        (t = (1:Interval) ∧ u = (0:Interval)))
      (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
      (e : OpenPartialHomeomorph S Plane)
      (W : Set S) (hW : IsOpen W)
      (hsub : (γ ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc a b ⊆ W ∩ e.source) :
      let g := γ ∘ Set.projIcc 0 1 zero_le_one
      ∃ E : OpenPartialHomeomorph S Plane,
        E.source ⊆ W ∩ e.source ∧
        Plane.closedSquare 0 1 ⊆ E.target ∧
        g '' Set.Icc a b ⊆ E.source ∧
        E (g a) = Plane.mk (-1) 0 ∧ E (g b) = Plane.mk 1 0 ∧
        (∀ x ∈ E.source, x ∈ Set.range γ ↔ E x 1 = 0) ∧
        {x : S | x ∈ E.source ∧ E x ∈ Plane.closedSquare 0 1} ∩ Set.range γ =
          g '' Set.Icc a b := by
    classical
    have hThreeArc :
        IsArcBetween (sideLeft ∪ (sideBottom ∪ sideRight)) cornerNW cornerNE := by
      apply isArcBetween_sideLeft.concatenate isArcBetween_lowerSides
      rintro z hz (hb | hr)
      · have hx := (mem_sideLeft.mp hz).1
        have hy := (mem_sideBottom.mp hb).1
        ext i
        fin_cases i
        · simpa [cornerSW] using hx
        · simpa [cornerSW] using hy
      · have hx := (mem_sideLeft.mp hz).1
        have hx' := (mem_sideRight.mp hr).1
        linarith
    
    have hThreeMeet :
        (sideLeft ∪ (sideBottom ∪ sideRight)) ∩ sideTop = {cornerNE,cornerNW} := by
      ext z
      constructor
      · rintro ⟨hl | hb | hr,ht⟩
        · right
          exact sideTop_meet_sideLeft z ht hl
        · have h1 := (mem_sideBottom.mp hb).1
          have h2 := (mem_sideTop.mp ht).1
          linarith
        · left
          have hx := (mem_sideRight.mp hr).1
          have hy := (mem_sideTop.mp ht).1
          ext i
          fin_cases i
          · simpa [cornerNE] using hx
          · simpa [cornerNE] using hy
      · rintro (rfl | rfl)
        · exact ⟨hThreeArc.right_mem,isArcBetween_sideTop.left_mem⟩
        · exact ⟨hThreeArc.left_mem,isArcBetween_sideTop.right_mem⟩
    have hplanarMatched {P : Set Schoenflies.Plane} {a b : Schoenflies.Plane}
        (hP : Schoenflies.IsArcBetween P a b) :
        ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
          F '' P = Schoenflies.sideTop ∧ F a = Schoenflies.cornerNE ∧ F b = Schoenflies.cornerNW := by
      obtain ⟨A, hA, hmeet, hJ⟩ := Schoenflies.exists_jordan_completion_of_isArcBetween hP
      let B := Schoenflies.sideLeft ∪ (Schoenflies.sideBottom ∪ Schoenflies.sideRight)
      obtain ⟨e, heimage, hea, heb⟩ :=
        Schoenflies.exists_homeomorph_union_arcs_preserving_second hA hP
          hThreeArc.reverse Schoenflies.isArcBetween_sideTop
          hmeet hThreeMeet
      have hmodel : B ∪ Schoenflies.sideTop = Schoenflies.modelCurve := by
        rw [Schoenflies.modelCurve_eq_sides]
        dsimp [B]
        ext z
        simp only [Set.mem_union]
        tauto
      let eModel := e.trans (Homeomorph.setCongr hmodel)
      obtain ⟨F, hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hJ
        Schoenflies.isJordanCurve_modelCurve eModel
      have hval (z : ↥(A ∪ P)) : F z.val = (e z).val := hF z
      refine ⟨F, ?_, ?_, ?_⟩
      · apply Set.Subset.antisymm
        · rintro y ⟨x, hx, rfl⟩
          rw [hval ⟨x, Or.inr hx⟩]
          have hm : (e ⟨x, Or.inr hx⟩).val ∈ Subtype.val ''
              (e '' {z : ↥(A ∪ P) | z.val ∈ P}) :=
            ⟨e ⟨x, Or.inr hx⟩, ⟨⟨x, Or.inr hx⟩, hx, rfl⟩, rfl⟩
          exact heimage.le hm
        · intro y hy
          rw [← heimage] at hy
          obtain ⟨z, ⟨x, hx, rfl⟩, hxy⟩ := hy
          exact ⟨x.val, hx, (hval x).trans hxy⟩
      · exact (hval ⟨a, Or.inl hA.left_mem⟩).trans (congrArg Subtype.val hea)
      · exact (hval ⟨b, Or.inl hA.right_mem⟩).trans (congrArg Subtype.val heb)
    let g : ℝ → S := γ ∘ Set.projIcc 0 1 zero_le_one
    have hg : Continuous g := hγ.comp continuous_projIcc
    have hgon (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : g t = γ ⟨t,ht⟩ := by
      simp only [g,Function.comp_apply,Set.projIcc_of_mem zero_le_one ht]
    have hginj (t u : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1)
        (he : g t = g u) : t = u := by
      rw [hgon t ⟨ht.1.le,ht.2.le⟩,hgon u hu] at he
      rcases hcoll _ _ he with h | h | h
      · exact congrArg Subtype.val h
      · have hh := congrArg Subtype.val h.1
        change t = 0 at hh
        linarith [ht.1]
      · have hh := congrArg Subtype.val h.1
        change t = 1 at hh
        linarith [ht.2]
    let O := g ⁻¹' (W ∩ e.source)
    have hO : IsOpen O := (hW.inter e.open_source).preimage hg
    obtain ⟨δ, hδ, hδO⟩ := isCompact_Icc.exists_cthickening_subset_open hO (fun t ht => hsub ⟨t,ht,rfl⟩)
    let ε := min δ (min a (1-b)) / 4
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεδ : ε ≤ δ := by dsimp [ε]; linarith [min_le_left δ (min a (1-b))]
    let A := a-ε
    let B := b+ε
    have hAB : A < B := by dsimp [A,B]; linarith
    have hA0 : 0 < A := by
      have hh := (min_le_right δ (min a (1-b))).trans (min_le_left a (1-b))
      dsimp [A,ε]; linarith
    have hB1 : B < 1 := by
      have hh := (min_le_right δ (min a (1-b))).trans (min_le_right a (1-b))
      dsimp [B,ε]; linarith
    have hgs (t : ℝ) (ht : t ∈ Set.Icc A B) : g t ∈ W ∩ e.source := by
      apply hδO
      by_cases hta : t < a
      · apply Metric.mem_cthickening_of_dist_le t a δ (Set.Icc a b) ⟨le_rfl,hab.le⟩
        rw [Real.dist_eq,abs_of_nonpos (by linarith)]
        dsimp [A] at ht
        linarith [ht.1]
      · by_cases htb : b < t
        · apply Metric.mem_cthickening_of_dist_le t b δ (Set.Icc a b) ⟨hab.le,le_rfl⟩
          rw [Real.dist_eq,abs_of_nonneg (by linarith)]
          dsimp [B] at ht
          linarith [ht.2]
        · exact Metric.self_subset_cthickening (Set.Icc a b) ⟨not_lt.mp hta,not_lt.mp htb⟩
    have hgi : Set.InjOn g (Set.Icc A B) := by
      intro t ht u hu he
      exact hginj t u ⟨hA0.trans_le ht.1,ht.2.trans_lt hB1⟩
        ⟨hA0.le.trans hu.1,hu.2.trans hB1.le⟩ he
    let f : ℝ → Schoenflies.Plane := fun t => e (g (A+(B-A)*t))
    have hparam (t : ℝ) (ht : t ∈ unitInterval) : A+(B-A)*t ∈ Set.Icc A B := by
      constructor <;> nlinarith [ht.1,ht.2]
    have hf : ContinuousOn f unitInterval :=
      e.continuousOn.comp (hg.comp (by fun_prop)).continuousOn (fun t ht => (hgs _ (hparam t ht)).2)
    have hfi : Set.InjOn f unitInterval := by
      intro t ht u hu he
      have hh := hgi (hparam t ht) (hparam u hu)
        (e.injOn (hgs _ (hparam t ht)).2 (hgs _ (hparam u hu)).2 he)
      nlinarith
    have hf0 : f 0 = e (g A) := by simp [f]
    have hf1 : f 1 = e (g B) := by simp [f]
    have himage : f '' unitInterval = (fun t => e (g t)) '' Set.Icc A B := by
      apply Set.Subset.antisymm
      · rintro z ⟨t,ht,rfl⟩; exact ⟨_,hparam t ht,rfl⟩
      · rintro z ⟨t,ht,rfl⟩
        let u := (t-A)/(B-A)
        have hu : u ∈ unitInterval := by
          constructor
          · exact div_nonneg (sub_nonneg.mpr ht.1) (by linarith)
          · exact (div_le_one (by linarith : 0 < B-A)).mpr (by linarith [ht.2])
        refine ⟨u,hu,?_⟩
        have hpu : A+(B-A)*u = t := by dsimp [u]; field_simp [ne_of_gt (sub_pos.mpr hAB)] <;> ring
        simp only [f,hpu]
    have hArc : Schoenflies.IsArcBetween (f '' unitInterval) (e (g A)) (e (g B)) :=
      ⟨f,hf,hfi,rfl,hf0,hf1⟩
    obtain ⟨F,hFP,hFA,hFB⟩ := hplanarMatched hArc
    have hFT : F '' ((fun t => e (g t)) '' Set.Icc A B) = Schoenflies.sideTop := by
      rwa [himage] at hFP
    have hcoord (t : ℝ) (ht : t ∈ Set.Icc A B) : F (e (g t)) 1 = 1 :=
      (Schoenflies.mem_sideTop.mp (hFT ▸ ⟨_,⟨t,ht,rfl⟩,rfl⟩)).1
    let q : ℝ → ℝ := fun t => F (e (g t)) 0
    have hqc : ContinuousOn q (Set.Icc A B) :=
      (EuclideanSpace.proj 0).continuous.continuousOn.comp
        (F.continuous.continuousOn.comp (e.continuousOn.comp hg.continuousOn
          (fun t ht => (hgs t ht).2)) (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)
    have hqi : Set.InjOn q (Set.Icc A B) := by
      intro t ht u hu he
      apply hgi ht hu
      apply e.injOn (hgs t ht).2 (hgs u hu).2
      apply F.injective
      ext i
      fin_cases i
      · exact he
      · exact (hcoord t ht).trans (hcoord u hu).symm
    have hqA : q A = 1 := by change F (e (g A)) 0 = 1; rw [hFA]; rfl
    have hqB : q B = -1 := by change F (e (g B)) 0 = -1; rw [hFB]; rfl
    have hanti : StrictAntiOn q (Set.Icc A B) :=
      ContinuousOn.strictAntiOn_of_injOn_Icc hAB.le (by rw [hqA,hqB]; norm_num) hqc hqi
    have haAB : a ∈ Set.Icc A B := by dsimp [A,B]; constructor <;> linarith
    have hbAB : b ∈ Set.Icc A B := by dsimp [A,B]; constructor <;> linarith
    have hqab : q b < q a := hanti haAB hbAB hab
    have hqa : q a < 1 := by rw [← hqA]; exact hanti ⟨le_rfl,hAB.le⟩ haAB (by dsimp [A]; linarith)
    have hqb : -1 < q b := by rw [← hqB]; exact hanti hbAB ⟨hAB.le,le_rfl⟩ (by dsimp [B]; linarith)
    let badParams : Set Interval := {t | t.val ≤ A ∨ B ≤ t.val}
    have hbadParams : IsClosed badParams :=
      (isClosed_le continuous_subtype_val continuous_const).union
        (isClosed_le continuous_const continuous_subtype_val)
    let bad := γ '' badParams
    have hbad : IsClosed bad :=
      (isCompact_univ.of_isClosed_subset hbadParams (subset_univ _)).image hγ |>.isClosed
    let N := (W ∩ e.source) ∩ badᶜ
    have hN : IsOpen N := (hW.inter e.open_source).inter hbad.isOpen_compl
    have hcoreN : g '' Set.Icc a b ⊆ N := by
      rintro x ⟨t,ht,rfl⟩
      refine ⟨hsub ⟨t,ht,rfl⟩,?_⟩
      rintro ⟨u,hu,he⟩
      have hut : t = u.val := hginj t u.val
        ⟨ha.trans_le ht.1,ht.2.trans_lt hb⟩ u.property
        (he.symm.trans (hgon u.val u.property).symm)
      rcases hu with hu | hu
      · dsimp [A] at hu; linarith [ht.1]
      · dsimp [B] at hu; linarith [ht.2]
    have hNcurve (x : S) (hx : x ∈ N) : x ∈ range γ ↔ x ∈ g '' Set.Icc A B := by
      constructor
      · rintro ⟨z,hz⟩
        have hzNot : ¬ (z.val ≤ A ∨ B ≤ z.val) := fun hn => hx.2 ⟨z,hn,hz⟩
        have hzA : A < z.val := lt_of_not_ge (fun hn => hzNot (Or.inl hn))
        have hzB : z.val < B := lt_of_not_ge (fun hn => hzNot (Or.inr hn))
        exact ⟨z.val,⟨hzA.le,hzB.le⟩,(hgon z.val z.property).trans hz⟩
      · rintro ⟨t,ht,rfl⟩
        exact ⟨⟨t,⟨hA0.le.trans ht.1,ht.2.trans hB1.le⟩⟩,(hgon t ⟨hA0.le.trans ht.1,ht.2.trans hB1.le⟩).symm⟩
    let V : Set Plane := {z | |z 0| < 1}
    have hV : IsOpen V := isOpen_lt ((EuclideanSpace.proj 0).continuous.abs) continuous_const
    let R := N ∩ (e.source ∩ e ⁻¹' (F ⁻¹' V))
    have hR : IsOpen R := hN.inter (e.isOpen_inter_preimage (hV.preimage F.continuous))
    let E₀ := (e.trans F.toOpenPartialHomeomorph).restr R
    have hE₀s : E₀.source = e.source ∩ R := by
      simp only [E₀, OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ, hR.interior_eq]
    have hE₀val (x : S) : E₀ x = F (e x) := rfl
    have hcoreE₀ (t : ℝ) (ht : t ∈ Icc a b) : g t ∈ E₀.source := by
      have htAB : t ∈ Icc A B := Icc_subset_Icc haAB.1 hbAB.2 ht
      have hqt : q t ∈ Icc (q b) (q a) :=
        ⟨hanti.antitoneOn htAB hbAB ht.2,hanti.antitoneOn haAB htAB ht.1⟩
      rw [hE₀s]
      exact ⟨(hgs t htAB).2,hcoreN ⟨t,ht,rfl⟩,(hgs t htAB).2,
        abs_lt.mpr ⟨hqb.trans_le hqt.1,hqt.2.trans_lt hqa⟩⟩
    have hflat (x : S) (hx : x ∈ E₀.source) : x ∈ range γ ↔ E₀ x 1 = 1 := by
      rw [hE₀s] at hx
      rw [hNcurve x hx.2.1,hE₀val]
      constructor
      · rintro ⟨t,ht,rfl⟩; exact hcoord t ht
      · intro hy
        have htop : F (e x) ∈ sideTop := mem_sideTop.mpr ⟨hy,hx.2.2.2.le⟩
        rw [← hFT] at htop
        obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := htop
        exact ⟨t,ht,e.injOn (hgs t ht).2 hx.1 (F.injective he)⟩
    let K := (fun t => E₀ (g t)) '' Icc a b
    have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
      (E₀.continuousOn.comp hg.continuousOn hcoreE₀)
    have hKt : K ⊆ E₀.target := by
      rintro z ⟨t,ht,rfl⟩; exact E₀.map_source (hcoreE₀ t ht)
    obtain ⟨d,hd,hdK⟩ := hK.exists_cthickening_subset_open E₀.open_target hKt
    let r := (q a-q b)/2
    let m := (q a+q b)/2
    have hr : 0 < r := by dsimp [r]; linarith
    let H : Plane ≃ₜ Plane := {
      toFun := fun z => Plane.mk ((m-z 0)/r) ((z 1-1)/d)
      invFun := fun z => Plane.mk (m-r*z 0) (1+d*z 1)
      left_inv := by
        intro z
        ext i
        fin_cases i <;> simp [Plane.mk]
        · field_simp [hr.ne'] <;> ring
        · field_simp [hd.ne'] <;> ring
      right_inv := by
        intro z
        ext i
        fin_cases i <;> simp [Plane.mk]
        · field_simp [hr.ne'] <;> ring
        · field_simp [hd.ne'] <;> ring
      continuous_toFun := by
        apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
        apply continuous_pi
        intro i
        fin_cases i <;> dsimp [Plane.mk] <;> fun_prop
      continuous_invFun := by
        apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
        apply continuous_pi
        intro i
        fin_cases i <;> dsimp [Plane.mk] <;> fun_prop }
    have hH0 (z : Plane) : H z 0 = (m-z 0)/r := rfl
    have hH1 (z : Plane) : H z 1 = (z 1-1)/d := rfl
    have hHi (z : Plane) : H.symm z = Plane.mk (m-r*z 0) (1+d*z 1) := rfl
    let E := E₀.trans H.toOpenPartialHomeomorph
    have hEs : E.source = E₀.source := by simp [E,OpenPartialHomeomorph.trans_source]
    have hEval (x : S) : E x = H (E₀ x) := rfl
    have hEa : E (g a) = Plane.mk (-1) 0 := by
      rw [hEval]
      ext i
      fin_cases i
      · change H (E₀ (g a)) 0 = -1
        rw [hH0]; change (m-q a)/r = -1
        dsimp [m,r]; field_simp [ne_of_gt (sub_pos.mpr hqab)] <;> ring
      · change H (E₀ (g a)) 1 = 0
        rw [hH1,hE₀val,hcoord a haAB]
        simp
    have hEb : E (g b) = Plane.mk 1 0 := by
      rw [hEval]
      ext i
      fin_cases i
      · change H (E₀ (g b)) 0 = 1
        rw [hH0]; change (m-q b)/r = 1
        dsimp [m,r]; field_simp [ne_of_gt (sub_pos.mpr hqab)] <;> ring
      · change H (E₀ (g b)) 1 = 0
        rw [hH1,hE₀val,hcoord b hbAB]
        simp
    have hqimage : q '' Icc a b = Icc (q b) (q a) :=
      ContinuousOn.image_Icc_of_antitoneOn hab.le (hqc.mono (Icc_subset_Icc haAB.1 hbAB.2))
        (hanti.antitoneOn.mono (Icc_subset_Icc haAB.1 hbAB.2))
    have hEt : E.target = H '' E₀.target := by simp [E, Homeomorph.image_eq_preimage_symm]
    have hsquare : Plane.closedSquare 0 1 ⊆ E.target := by
      intro z hz
      have hzsup : Plane.supNorm z ≤ 1 := mem_closedSquare_zero_one.mp hz
      have hz0 := abs_le.mp ((Plane.abs_zero_le_supNorm z).trans hzsup)
      have hz1 := abs_le.mp ((Plane.abs_one_le_supNorm z).trans hzsup)
      have hx : m-r*z 0 ∈ Icc (q b) (q a) := by
        dsimp [m,r]; constructor <;> nlinarith [hz0.1,hz0.2]
      rw [← hqimage] at hx
      obtain ⟨t,ht,hqt⟩ := hx
      have htK : E₀ (g t) ∈ K := ⟨t,ht,rfl⟩
      have hnear : dist (H.symm z) (E₀ (g t)) ≤ d := by
        have hplane : H.symm z-E₀ (g t) = (d*z 1) • Plane.mk 0 1 := by
          ext i
          fin_cases i
          · simp only [hHi,Plane.mk,PiLp.sub_apply,PiLp.smul_apply]
            change m-r*z 0-q t = (d*z 1)*0
            rw [hqt]; ring
          · simp only [hHi,Plane.mk,PiLp.sub_apply,PiLp.smul_apply]
            change 1+d*z 1-E₀ (g t) 1 = (d*z 1)*1
            rw [hE₀val,hcoord t (Icc_subset_Icc haAB.1 hbAB.2 ht)]
            ring
        rw [dist_eq_norm,hplane]
        simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos hd]
        have hn : ‖Plane.mk 0 1‖ = 1 := by
          simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
        rw [hn,mul_one]
        nlinarith [(abs_le.mpr hz1 : |z 1| ≤ 1)]
      have htgt : H.symm z ∈ E₀.target := hdK
        (Metric.mem_cthickening_of_dist_le _ _ d K htK hnear)
      rw [hEt]
      exact ⟨H.symm z,htgt,H.apply_symm_apply z⟩
    refine ⟨E,?_,hsquare,?_,hEa,hEb,?_,?_⟩
    · intro x hx
      rw [hEs,hE₀s] at hx
      exact hx.2.1.1
    · rintro x ⟨t,ht,rfl⟩; rw [hEs]; exact hcoreE₀ t ht
    · intro x hx
      rw [hEs] at hx
      rw [hEval,hH1,hflat x hx]
      exact ⟨fun h => by rw [h]; simp,fun h => by
        have hh := (div_eq_zero_iff).mp h
        exact sub_eq_zero.mp (hh.resolve_right hd.ne')⟩
    · apply Set.Subset.antisymm
      · rintro x ⟨⟨hx,hxs⟩,hxc⟩
        have hx₀ : x ∈ E₀.source := hEs ▸ hx
        have hxR := hE₀s ▸ hx₀
        obtain ⟨t,ht,hxt⟩ := (hNcurve x hxR.2.1).mp hxc
        have hxsup := mem_closedSquare_zero_one.mp hxs
        have hxx := abs_le.mp ((Plane.abs_zero_le_supNorm (E x)).trans hxsup)
        rw [hEval,hH0] at hxx
        have hqtx : E₀ x 0 = q t := by rw [← hxt]; rfl
        rw [hqtx] at hxx
        have hqt : q t ∈ Icc (q b) (q a) := by
          have hl := (le_div_iff₀ hr).mp hxx.1
          have hu := (div_le_iff₀ hr).mp hxx.2
          dsimp [m,r] at hl hu
          constructor <;> linarith
        have hta : a ≤ t := by
          by_contra hn
          have := hanti ht haAB (not_le.mp hn)
          linarith [hqt.2]
        have htb : t ≤ b := by
          by_contra hn
          have := hanti hbAB ht (not_le.mp hn)
          linarith [hqt.1]
        exact ⟨t,⟨hta,htb⟩,hxt⟩
      · rintro x ⟨t,ht,rfl⟩
        have htAB := Icc_subset_Icc haAB.1 hbAB.2 ht
        have hqt : q t ∈ Icc (q b) (q a) :=
          ⟨hanti.antitoneOn htAB hbAB ht.2,hanti.antitoneOn haAB htAB ht.1⟩
        refine ⟨⟨hEs.symm ▸ hcoreE₀ t ht,?_⟩,⟨t,⟨ha.le.trans ht.1,ht.2.trans hb.le⟩⟩,(hgon t ⟨ha.le.trans ht.1,ht.2.trans hb.le⟩).symm⟩
        rw [mem_closedSquare_zero_one]
        change max |E (g t) 0| |E (g t) 1| ≤ 1
        apply max_le
        · rw [hEval,hH0]
          change |(m-q t)/r| ≤ 1
          apply abs_le.mpr
          constructor
          · apply (le_div_iff₀ hr).mpr
            dsimp [m,r]; linarith [hqt.2]
          · apply (div_le_iff₀ hr).mpr
            dsimp [m,r]; linarith [hqt.1]
        · rw [hEval,hH1,hE₀val,hcoord t htAB]
          norm_num
  
  
  let C : K → Set S := fun k => (γ k ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (a k) (b k)
  have hcompact (k : K) : IsCompact (C k) :=
    isCompact_Icc.image ((hγ k).comp continuous_projIcc)
  have hpairs (i j : K) : ∃ A B : Set S,
      IsOpen A ∧ IsOpen B ∧ C i ⊆ A ∧ C j ⊆ B ∧ (i ≠ j → Disjoint A B) := by
    by_cases hij : i = j
    · exact ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ,
        Set.subset_univ _, Set.subset_univ _, fun h => (h hij).elim⟩
    · obtain ⟨A, B, hA, hB, hCA, hCB, hAB⟩ :=
        normal_separation (hcompact i).isClosed (hcompact j).isClosed (hdis i j hij)
      exact ⟨A, B, hA, hB, hCA, hCB, fun _ => hAB⟩
  choose A B hA hB hCA hCB hAB using hpairs
  let W : K → Set S := fun i => ⋂ j, A i j ∩ B j i
  have hW (i : K) : IsOpen (W i) :=
    isOpen_iInter_of_finite (fun j => (hA i j).inter (hB j i))
  have hCW (i : K) : C i ⊆ W i := by
    intro x hx
    exact Set.mem_iInter.mpr (fun j => ⟨hCA i j hx, hCB j i hx⟩)
  have hWW (i j : K) (hij : i ≠ j) : Disjoint (W i) (W j) := by
    apply (hAB i j hij).mono
    · intro x hx
      exact ((Set.mem_iInter.mp hx) j).1
    · intro x hx
      exact ((Set.mem_iInter.mp hx) i).2
  have hcharts (k : K) := hchart (γ k) (hγ k) (hcoll k)
    (a k) (b k) (ha k) (hab k) (hb k) (e k) (W k) (hW k)
    (fun x hx => ⟨hCW k hx, hsub k hx⟩)
  choose E hEW hSquare hArc hleft hright hflat hExact using hcharts
  refine ⟨E, ?_, ?_, hSquare, hArc, ?_, hflat, hExact⟩
  · intro k x hx
    exact (hEW k hx).2
  · intro i j hij
    exact (hWW i j hij).mono
      (fun x hx => (hEW i hx).1) (fun x hx => (hEW j hx).1)
  · intro k
    exact ⟨hleft k, hright k⟩

#print axioms finite_actual_interval_compatible_crosscut_charts
