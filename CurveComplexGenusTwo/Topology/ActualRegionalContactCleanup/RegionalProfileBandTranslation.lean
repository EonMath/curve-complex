import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip

open CurveComplex Set Topology

/-- Translate an embedded strip transversely, fixing its outer edges and
    extending by the identity outside its range. -/
theorem regional_closed_band_profile_translation_ambient_isotopy
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,X))
    (hE : Topology.IsEmbedding E)
    (hU : IsOpen (E '' {z | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1}))
    (ε : C(Interval,ℝ)) (hε0 : ∀ t, 0 ≤ ε t) (hε1 : ∀ t, ε t < 1) :
    ∃ H : AmbientIsotopy X,
      (∀ (s : Interval) (z : Interval × Set.Icc (-1 : ℝ) 1),
        ∃ w : Set.Icc (-1 : ℝ) 1,
          (w : ℝ) = (z.2 : ℝ) + (s : ℝ)*ε z.1*(1-|(z.2 : ℝ)|) ∧
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
  have clock_bounds (s t : Interval) :
      0 ≤ (s : ℝ)*ε t ∧ (s : ℝ)*ε t < 1 :=
    ⟨mul_nonneg s.property.1 (hε0 t),
      (mul_le_of_le_one_left (hε0 t) s.property.2).trans_lt (hε1 t)⟩
  have width_bound (s t : Interval) (w : Set.Icc (-1 : ℝ) 1) :
      (w : ℝ)+(s : ℝ)*ε t*(1-|(w : ℝ)|) ∈ Set.Icc (-1 : ℝ) 1 := by
    obtain ⟨h,heq,hL,hR⟩ := width_homeomorph ((s : ℝ)*ε t)
      (clock_bounds s t).1 (clock_bounds s t).2
    exact heq w ▸ (h w).property
  let k : Interval × (Interval × Set.Icc (-1 : ℝ) 1) →
      Interval × Set.Icc (-1 : ℝ) 1 :=
    fun z => (z.2.1,⟨(z.2.2 : ℝ)+(z.1 : ℝ)*ε z.2.1*(1-|(z.2.2 : ℝ)|),
      width_bound z.1 z.2.1 z.2.2⟩)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hkbij (s : Interval) : Function.Bijective (fun z => k (s,z)) := by
    have hlocal (t : Interval) := width_homeomorph ((s : ℝ)*ε t)
      (clock_bounds s t).1 (clock_bounds s t).2
    constructor
    · intro z w he
      have h1 := congrArg Prod.fst he
      change z.1 = w.1 at h1
      obtain ⟨h,heq,hL,hR⟩ := hlocal z.1
      have h2 := congrArg (fun q => (q.2 : ℝ)) he
      change (z.2 : ℝ)+(s : ℝ)*ε z.1*(1-|(z.2 : ℝ)|) =
        (w.2 : ℝ)+(s : ℝ)*ε w.1*(1-|(w.2 : ℝ)|) at h2
      rw [← h1,← heq z.2,← heq w.2] at h2
      exact Prod.ext h1 (h.injective (Subtype.ext h2))
    · intro z
      obtain ⟨h,heq,hL,hR⟩ := hlocal z.1
      refine ⟨(z.1,h.symm z.2),Prod.ext rfl ?_⟩
      apply Subtype.ext
      change (h.symm z.2 : ℝ)+(s : ℝ)*ε z.1*(1-|(h.symm z.2 : ℝ)|) = (z.2 : ℝ)
      rw [← heq,h.apply_symm_apply]
  have hk0 (z : Interval × Set.Icc (-1 : ℝ) 1) : k (0,z) = z := by
    refine Prod.ext (show (k (0,z)).1 = z.1 from rfl) ?_
    apply Subtype.ext
    change (z.2 : ℝ)+0*ε z.1*(1-|(z.2 : ℝ)|) = (z.2 : ℝ)
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
        change (z.2 : ℝ)+(s : ℝ)*ε z.1*(1-|(z.2 : ℝ)|) = (z.2 : ℝ)
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

#print axioms regional_closed_band_profile_translation_ambient_isotopy

