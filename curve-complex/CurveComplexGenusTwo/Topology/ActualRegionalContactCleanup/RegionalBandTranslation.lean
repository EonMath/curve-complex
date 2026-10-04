import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_closed_band_transverse_translation_ambient_isotopy
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,X))
    (hE : Topology.IsEmbedding E)
    (hU : IsOpen (E '' {z | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1}))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ H : AmbientIsotopy X,
      (∀ (s : Interval) (z : Interval × Set.Icc (-1 : ℝ) 1),
        ∃ w : Set.Icc (-1 : ℝ) 1,
          (w : ℝ) = (z.2 : ℝ) + (s : ℝ)*ε*(1-|(z.2 : ℝ)|) ∧
          H.map (s,E z) = E (z.1,w)) ∧
      ∀ (s : Interval) (y : X), y ∉ Set.range E → H.map (s,y) = y := by
  classical
  have width_homeomorph (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
      ∃ h : Set.Icc (-1 : ℝ) 1 ≃ₜ Set.Icc (-1 : ℝ) 1,
        (∀ w, (h w : ℝ) = (w : ℝ) + c*(1-|(w : ℝ)|)) ∧
        h ⟨-1,by norm_num⟩ = ⟨-1,by norm_num⟩ ∧
        h ⟨1,by norm_num⟩ = ⟨1,by norm_num⟩ := by
    let f : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1 := fun w =>
      ⟨(w : ℝ)+c*(1-|(w : ℝ)|),by
        by_cases hw : 0 ≤ (w : ℝ)
        · rw [abs_of_nonneg hw]
          have h0 := mul_nonneg (sub_nonneg.mpr hc1.le) hw
          have h1 := mul_nonneg (sub_nonneg.mpr hc1.le)
            (sub_nonneg.mpr w.property.2)
          constructor <;> nlinarith only [h0,h1,hc0]
        · have hw0 := le_of_not_ge hw
          rw [abs_of_nonpos hw0]
          have hp : 0 ≤ 1+c := by linarith only [hc0]
          have h0 := mul_nonneg hp
            (show 0 ≤ (w : ℝ)+1 by linarith only [w.property.1])
          have h1 := mul_nonneg hp (neg_nonneg.mpr hw0)
          constructor <;> nlinarith only [h0,h1,hc1]⟩
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hmono : StrictMono f := by
      intro w v hv
      change (w : ℝ)+c*(1-|(w : ℝ)|) <
        (v : ℝ)+c*(1-|(v : ℝ)|)
      have hvv : (w : ℝ) < (v : ℝ) := hv
      by_cases hw : 0 ≤ (w : ℝ)
      · rw [abs_of_nonneg hw,abs_of_nonneg (hw.trans hvv.le)]
        have hp := mul_pos (sub_pos.mpr hc1) (sub_pos.mpr hvv)
        nlinarith only [hp]
      · by_cases hv0 : (v : ℝ) ≤ 0
        · rw [abs_of_nonpos (le_of_not_ge hw),abs_of_nonpos hv0]
          have hp := mul_pos (show 0 < 1+c by linarith only [hc0])
            (sub_pos.mpr hvv)
          nlinarith only [hp]
        · rw [abs_of_neg (lt_of_not_ge hw),abs_of_pos (lt_of_not_ge hv0)]
          have hp := mul_pos (show 0 < 1+c by linarith only [hc0])
            (neg_pos.mpr (lt_of_not_ge hw))
          have hq := mul_pos (sub_pos.mpr hc1) (lt_of_not_ge hv0)
          nlinarith only [hp,hq]
    have hfL : f ⟨-1,by norm_num⟩ = ⟨-1,by norm_num⟩ :=
      Subtype.ext (by norm_num [f])
    have hfR : f ⟨1,by norm_num⟩ = ⟨1,by norm_num⟩ :=
      Subtype.ext (by norm_num [f])
    let : PreconnectedSpace (Set.Icc (-1 : ℝ) 1) :=
      Subtype.preconnectedSpace isPreconnected_Icc
    have hsurj : Function.Surjective f := by
      intro w
      exact mem_range_of_exists_le_of_exists_ge hf
        ⟨⟨-1,by norm_num⟩,by rw [hfL]; exact w.property.1⟩
        ⟨⟨1,by norm_num⟩,by rw [hfR]; exact w.property.2⟩
    let h := (Equiv.ofBijective f ⟨hmono.injective,hsurj⟩).toHomeomorphOfContinuousClosed
      hf hf.isClosedMap
    exact ⟨h,fun w => rfl,hfL,hfR⟩
  have clock_bounds (s : Interval) :
      0 ≤ (s : ℝ)*ε ∧ (s : ℝ)*ε < 1 :=
    ⟨mul_nonneg s.property.1 hε0,
      (mul_le_of_le_one_left hε0 s.property.2).trans_lt hε1⟩
  have width_bound (s : Interval) (w : Set.Icc (-1 : ℝ) 1) :
      (w : ℝ)+(s : ℝ)*ε*(1-|(w : ℝ)|) ∈ Set.Icc (-1 : ℝ) 1 := by
    obtain ⟨h,heq,hL,hR⟩ := width_homeomorph ((s : ℝ)*ε)
      (clock_bounds s).1 (clock_bounds s).2
    exact heq w ▸ (h w).property
  let k : Interval × (Interval × Set.Icc (-1 : ℝ) 1) →
      Interval × Set.Icc (-1 : ℝ) 1 :=
    fun z => (z.2.1,⟨(z.2.2 : ℝ)+(z.1 : ℝ)*ε*(1-|(z.2.2 : ℝ)|),
      width_bound z.1 z.2.2⟩)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hkbij (s : Interval) : Function.Bijective (fun z => k (s,z)) := by
    obtain ⟨h,heq,hL,hR⟩ := width_homeomorph ((s : ℝ)*ε)
      (clock_bounds s).1 (clock_bounds s).2
    have hkw (z : Interval × Set.Icc (-1 : ℝ) 1) : (k (s,z)).2 = h z.2 :=
      Subtype.ext (heq z.2).symm
    constructor
    · intro z w he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      rw [hkw z,hkw w] at h2
      exact Prod.ext h1 (h.injective h2)
    · intro z
      refine ⟨(z.1,h.symm z.2),?_⟩
      exact Prod.ext rfl ((hkw _).trans (h.apply_symm_apply z.2))
  have hk0 (z : Interval × Set.Icc (-1 : ℝ) 1) : k (0,z) = z := by
    refine Prod.ext (show (k (0,z)).1 = z.1 from rfl) ?_
    apply Subtype.ext
    change (z.2 : ℝ)+0*ε*(1-|(z.2 : ℝ)|) = (z.2 : ℝ)
    ring
  let d := hE.toHomeomorph
  let U := E '' {z | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1}
  let A := Set.range E
  let F : Interval × X → X := fun z =>
    if hy : z.2 ∈ A then E (k (z.1,d.symm ⟨z.2,hy⟩)) else z.2
  have hdinv (y : X) (hy : y ∈ A) : E (d.symm ⟨y,hy⟩) = y :=
    congrArg (fun y : Set.range E => y.val) (d.apply_symm_apply ⟨y,hy⟩)
  have hde (z : Interval × Set.Icc (-1 : ℝ) 1) :
      d.symm ⟨E z,Set.mem_range_self z⟩ = z := d.symm_apply_apply z
  have hband (s : Interval) (z : Interval × Set.Icc (-1 : ℝ) 1) :
      F (s,E z) = E (k (s,z)) := by
    dsimp only [F]
    rw [dite_eq_left (show E z ∈ A from Set.mem_range_self z),hde z]
  have hout (s : Interval) (y : X) (hy : y ∉ A) : F (s,y) = y := by
    dsimp only [F]
    rw [dite_eq_right hy]
  have hfixed (s : Interval) (y : X) (hy : y ∉ U) : F (s,y) = y := by
    by_cases hyA : y ∈ A
    · let z := d.symm ⟨y,hyA⟩
      have hzy : E z = y := hdinv y hyA
      have hw : |(z.2 : ℝ)| = 1 := by
        by_cases hl : (-1 : ℝ) < (z.2 : ℝ)
        · have hr : ¬(z.2 : ℝ) < 1 := fun he => hy ⟨z,⟨hl,he⟩,hzy⟩
          have he : (z.2 : ℝ) = 1 :=
            le_antisymm z.2.property.2 (not_lt.mp hr)
          rw [he,abs_one]
        · have he : (z.2 : ℝ) = -1 :=
            le_antisymm (not_lt.mp hl) z.2.property.1
          rw [he,abs_neg,abs_one]
      have hkz : k (s,z) = z := by
        refine Prod.ext (show (k (s,z)).1 = z.1 from rfl) ?_
        apply Subtype.ext
        change (z.2 : ℝ)+(s : ℝ)*ε*(1-|(z.2 : ℝ)|) = (z.2 : ℝ)
        rw [hw]
        ring
      dsimp only [F]
      rw [dite_eq_left hyA]
      change E (k (s,z)) = y
      rw [hkz,hzy]
    · exact hout s y hyA
  let P : Set (Interval × X) := Set.univ ×ˢ A
  let Qe : Set (Interval × X) := Set.univ ×ˢ Uᶜ
  have hA : IsClosed A := (isCompact_range E.continuous).isClosed
  have hP : IsClosed P := isClosed_univ.prod hA
  have hQ : IsClosed Qe := isClosed_univ.prod hU.isClosed_compl
  have hFP : ContinuousOn F P := by
    rw [continuousOn_iff_continuous_domRestrict]
    let j : P → Set.range E := fun z => ⟨z.val.2,z.property.2⟩
    have hj : Continuous j :=
      (continuous_snd.comp continuous_subtype_val).subtype_mk _
    have hcont : Continuous (fun z : P => E (k (z.val.1,d.symm (j z)))) :=
      E.continuous.comp (hkc.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          (d.symm.continuous.comp hj)))
    convert hcont using 1
    funext z
    dsimp only [Set.domRestrict,F]
    rw [dite_eq_left z.property.2]
  have hFQ : ContinuousOn F Qe := by
    apply continuous_snd.continuousOn.congr
    intro z hz
    exact hfixed z.1 z.2 hz.2
  have hcover : P ∪ Qe = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    by_cases hz : z.2 ∈ A
    · exact Or.inl ⟨Set.mem_univ _,hz⟩
    · exact Or.inr ⟨Set.mem_univ _,fun he => hz (Set.image_subset_range _ _ he)⟩
  have hFc : Continuous F := by
    have hc := hFP.union_of_isClosed hFQ hP hQ
    rw [hcover] at hc
    exact continuousOn_univ.mp hc
  have hFbij (s : Interval) : Function.Bijective (fun y => F (s,y)) := by
    constructor
    · intro y z he
      change F (s,y) = F (s,z) at he
      by_cases hy : y ∈ A
      · obtain ⟨a,ha⟩ := hy
        by_cases hz : z ∈ A
        · obtain ⟨b,hb⟩ := hz
          rw [←ha,←hb,hband,hband] at he
          exact ha.symm.trans
            ((congrArg E ((hkbij s).1 (hE.injective he))).trans hb)
        · rw [←ha,hband,hout s z hz] at he
          exact False.elim (hz ⟨k (s,a),he⟩)
      · by_cases hz : z ∈ A
        · obtain ⟨b,hb⟩ := hz
          rw [←hb,hout s y hy,hband] at he
          exact False.elim (hy ⟨k (s,b),he.symm⟩)
        · rw [hout s y hy,hout s z hz] at he
          exact he
    · intro y
      by_cases hy : y ∈ A
      · obtain ⟨z,hz⟩ := hy
        obtain ⟨w,hw⟩ := (hkbij s).2 z
        exact ⟨E w,(hband s w).trans ((congrArg E hw).trans hz)⟩
      · exact ⟨y,hout s y hy⟩
  let H : AmbientIsotopy X :=
    { map := ⟨F,hFc⟩,
      homeomorphism_at := by
        intro s
        have hc : Continuous (fun y => F (s,y)) :=
          hFc.comp (continuous_const.prodMk continuous_id)
        let h := (Equiv.ofBijective (fun y => F (s,y)) (hFbij s)).toHomeomorphOfContinuousClosed
          hc hc.isClosedMap
        exact ⟨h,fun y => rfl⟩,
      at_zero := by
        intro y
        by_cases hy : y ∈ A
        · obtain ⟨z,hz⟩ := hy
          rw [←hz]
          exact (hband 0 z).trans (congrArg E (hk0 z))
        · exact hout 0 y hy }
  refine ⟨H,?_,hout⟩
  intro s z
  exact ⟨(k (s,z)).2,rfl,hband s z⟩

theorem regional_proper_strip_parallel_ambient_move
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBFront : B ⊆ frontier F)
    (N : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hN : Topology.IsEmbedding N)
    (hend : ∀ w, (N (0,w)).val ∈ B ∧ (N (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (N (t,w)).val ∈ interior F)
    (hopen : IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1})) :
    ∃ H : AmbientIsotopy ↥F,
      (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ B} =
        {y : ↥F | y.val ∈ B}) ∧
      (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
        {y : ↥F | y.val ∈ frontier F}) ∧
      H.finalMap '' Set.range (fun t : Interval => N (t,⟨0,by norm_num⟩)) =
        Set.range (fun t : Interval => N (t,⟨(1/2 : ℝ),by norm_num⟩)) ∧
      ∀ t y, y ∉ Set.range N → H.map (t,y) = y := by
  let : CompactSpace ↥F := isCompact_iff_compactSpace.mp hF
  let ε : ℝ := 1/2
  have hε0 : 0 ≤ ε := by norm_num [ε]
  have hε1 : ε < 1 := by norm_num [ε]
  obtain ⟨H,hband,houtside⟩ :=
    regional_closed_band_transverse_translation_ambient_isotopy
      N hN hopen ε hε0 hε1
  have hNboundary (z : Interval × Set.Icc (-1 : ℝ) 1) :
      (N z).val ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
    constructor
    · intro hz
      by_cases h0 : z.1 = 0
      · exact Or.inl h0
      · by_cases h1 : z.1 = 1
        · exact Or.inr h1
        · have ht : z.1 ∈ Set.Ioo (0 : Interval) 1 :=
            ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩
          exact False.elim
            ((mem_interior_iff_notMem_frontier
              (interior_subset (hint z.1 ht z.2))).mp (hint z.1 ht z.2)
                (hBFront hz))
    · rintro (h0 | h1)
      · have hz : z = (0,z.2) := Prod.ext h0 rfl
        rw [hz]
        exact (hend z.2).1
      · have hz : z = (1,z.2) := Prod.ext h1 rfl
        rw [hz]
        exact (hend z.2).2
  have hNfront (z : Interval × Set.Icc (-1 : ℝ) 1) :
      (N z).val ∈ frontier F ↔ z.1 = 0 ∨ z.1 = 1 := by
    constructor
    · intro hz
      by_cases h0 : z.1 = 0
      · exact Or.inl h0
      · by_cases h1 : z.1 = 1
        · exact Or.inr h1
        · have ht : z.1 ∈ Set.Ioo (0 : Interval) 1 :=
            ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩
          exact False.elim
            ((mem_interior_iff_notMem_frontier
              (interior_subset (hint z.1 ht z.2))).mp (hint z.1 ht z.2) hz)
    · intro hz
      exact hBFront ((hNboundary z).mpr hz)
  have hpreserve (D : Set S)
      (hD : ∀ z : Interval × Set.Icc (-1 : ℝ) 1,
        (N z).val ∈ D ↔ z.1 = 0 ∨ z.1 = 1)
      (t : Interval) (y : ↥F) :
      (H.map (t,y)).val ∈ D ↔ y.val ∈ D := by
    by_cases hy : y ∈ Set.range N
    · obtain ⟨z,rfl⟩ := hy
      obtain ⟨w,hw,hHz⟩ := hband t z
      rw [hHz,hD (z.1,w),hD z]
    · rw [houtside t y hy]
  have himage (D : Set S)
      (hD : ∀ z : Interval × Set.Icc (-1 : ℝ) 1,
        (N z).val ∈ D ↔ z.1 = 0 ∨ z.1 = 1)
      (t : Interval) :
      (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ D} =
        {y : ↥F | y.val ∈ D} := by
    apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      exact (hpreserve D hD t z).mpr hz
    · intro y hy
      obtain ⟨h,hh⟩ := H.homeomorphism_at t
      have he : H.map (t,h.symm y) = y :=
        (hh _).symm.trans (h.apply_symm_apply y)
      exact ⟨h.symm y,
        (hpreserve D hD t (h.symm y)).mp (he.symm ▸ hy),he⟩
  refine ⟨H,fun t => himage B hNboundary t,
    fun t => himage (frontier F) hNfront t,?_,houtside⟩
  change (fun y => H.map (1,y)) ''
      Set.range (fun t : Interval => N (t,⟨0,by norm_num⟩)) =
      Set.range (fun t : Interval => N (t,⟨(1/2 : ℝ),by norm_num⟩))
  ext y
  constructor
  · rintro ⟨z,⟨t,rfl⟩,rfl⟩
    obtain ⟨w,hw,hHw⟩ := hband 1 (t,⟨0,by norm_num⟩)
    have hwidth : w = ⟨(1/2 : ℝ),by norm_num⟩ := by
      apply Subtype.ext
      change (w : ℝ) = ε
      simpa [ε] using hw
    rw [hwidth] at hHw
    exact ⟨t,hHw.symm⟩
  · rintro ⟨t,rfl⟩
    refine ⟨N (t,⟨0,by norm_num⟩),⟨t,rfl⟩,?_⟩
    obtain ⟨w,hw,hHw⟩ := hband 1 (t,⟨0,by norm_num⟩)
    have hwidth : w = ⟨(1/2 : ℝ),by norm_num⟩ := by
      apply Subtype.ext
      change (w : ℝ) = ε
      simpa [ε] using hw
    simpa [hwidth] using hHw

theorem regional_proper_strip_ambient_parallel_copy
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBFront : B ⊆ frontier F)
    (a : C(Interval, ↥F))
    (N : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hN : Topology.IsEmbedding N)
    (hcenter : ∀ t, N (t,⟨0,by norm_num⟩) = a t)
    (hend : ∀ w, (N (0,w)).val ∈ B ∧ (N (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (N (t,w)).val ∈ interior F)
    (hopen : IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1})) :
    ∃ b : C(Interval,↥F),
      Topology.IsEmbedding b ∧
      (b 0).val ∈ B ∧ (b 1).val ∈ B ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1,
        (b t).val ∉ frontier F) ∧
      Disjoint (Set.range a) (Set.range b) ∧
      Set.range b ⊆ Set.range N ∧
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ B} =
          {y : ↥F | y.val ∈ B}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a = Set.range b ∧
        (∀ t y, y ∉ Set.range N → H.map (t,y) = y) := by
  let width : Set.Icc (-1 : ℝ) 1 := ⟨1/2,by norm_num⟩
  let b : C(Interval,↥F) :=
    ⟨fun t => N (t,width),
      N.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hb : Topology.IsEmbedding b :=
    (b.continuous.isClosedEmbedding (by
      intro s t he
      exact congrArg Prod.fst (hN.injective he))).isEmbedding
  have hbproper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (b t).val ∉ frontier F := by
    intro t ht
    exact (mem_interior_iff_notMem_frontier
      (interior_subset (hint t ht width))).mp (hint t ht width)
  have hdisjoint : Disjoint (Set.range a) (Set.range b) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t,ht⟩ ⟨u,hu⟩
    have he : N (t,⟨0,by norm_num⟩) = N (u,width) :=
      (hcenter t).trans (ht.trans hu.symm)
    have hw := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2 : ℝ))
      (hN.injective he)
    norm_num [width] at hw
  obtain ⟨H,hHB,hHF,hHrange,houtside⟩ :=
    regional_proper_strip_parallel_ambient_move F B hF hBFront
      N hN hend hint hopen
  refine ⟨b,hb,(hend width).1,(hend width).2,hbproper,hdisjoint,
    (by rintro y ⟨t,rfl⟩; exact ⟨(t,width),rfl⟩),
    H,hHB,hHF,?_,houtside⟩
  have harange : Set.range a =
      Set.range (fun t : Interval => N (t,⟨0,by norm_num⟩)) := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨t,hcenter t⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,(hcenter t).symm⟩
  rw [harange]
  exact hHrange

theorem regional_proper_strip_supported_ambient_parallel_copy
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBFront : B ⊆ frontier F)
    (a : C(Interval, ↥F))
    (N : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hN : Topology.IsEmbedding N)
    (hcenter : ∀ t, N (t,⟨0,by norm_num⟩) = a t)
    (hend : ∀ w, (N (0,w)).val ∈ B ∧ (N (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (N (t,w)).val ∈ interior F)
    (hopen : IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (O : Set ↥F) (hO : IsOpen O) (haO : Set.range a ⊆ O) :
    ∃ b : C(Interval,↥F),
      Topology.IsEmbedding b ∧
      (b 0).val ∈ B ∧ (b 1).val ∈ B ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1,
        (b t).val ∉ frontier F) ∧
      Disjoint (Set.range a) (Set.range b) ∧
      Set.range b ⊆ O ∧
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ B} =
          {y : ↥F | y.val ∈ B}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a = Set.range b ∧
        (∀ t y, y ∉ O → H.map (t,y) = y) := by
  obtain ⟨ρ,hρ,n,hn,hnO,hnformula,hncenter⟩ :=
    source_shrink_embedded_strip_in_open N hN O hO
      (fun t => haO ⟨t,(hcenter t).symm⟩)
  let M : C(Interval × Set.Icc (-1 : ℝ) 1,↥F) := ⟨n,hn.continuous⟩
  have hMc : ∀ t, M (t,⟨0,by norm_num⟩) = a t :=
    fun t => (hncenter t).trans (hcenter t)
  have hMend : ∀ w, (M (0,w)).val ∈ B ∧ (M (1,w)).val ∈ B := by
    intro w
    change (n (0,w)).val ∈ B ∧ (n (1,w)).val ∈ B
    rw [hnformula,hnformula]
    exact hend _
  have hMint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (M (t,w)).val ∈ interior F := by
    intro t ht w
    change (n (t,w)).val ∈ interior F
    rw [hnformula]
    exact hint t ht _
  have hMopen : IsOpen
      (M '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) :=
    regional_strip_narrow_open_core F F (Set.Subset.refl F)
      N hN hopen ρ hρ.1 hρ.2 M
      (fun z => congrArg Subtype.val (hnformula z))
  obtain ⟨b,hb,hb0,hb1,hbi,hdisjoint,hbM,H,hHB,hHF,hHmove,hHoutside⟩ :=
    regional_proper_strip_ambient_parallel_copy F B hF hBFront a M hn
      hMc hMend hMint hMopen
  refine ⟨b,hb,hb0,hb1,hbi,hdisjoint,hbM.trans hnO,
    H,hHB,hHF,hHmove,?_⟩
  intro t y hyO
  exact hHoutside t y (fun hyM => hyO (hnO hyM))

#print axioms regional_closed_band_transverse_translation_ambient_isotopy
#print axioms regional_proper_strip_parallel_ambient_move
#print axioms regional_proper_strip_ambient_parallel_copy
#print axioms regional_proper_strip_supported_ambient_parallel_copy
