import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ActualHyperbolicComponentCoverPlanePROVED

namespace CurveComplex.Hyperbolic
open Filter Topology Set Matrix
open scoped Manifold ContDiff UpperHalfPlane ENNReal unitInterval MatrixGroups

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Source Fact 3.5(G1), actual geometric development of the simply connected
cover of the literal source metric component. This exposes the locally
metric-preserving development constructed in the approved plane producer;
no development or axis certificate is supplied as a premise. -/
theorem actual_hyperbolic_component_simply_connected_cover_develops
    {P : Type} [TopologicalSpace P] [SimplyConnectedSpace P]
    (H : ClosedHyperbolicMetric E) (base : E)
    (p : P → connectedComponent base)
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    ∃ e : P ≃ₜ H2, ∀ x : P, ∃ U : Set P,
      IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          @dist E H.metric.toDist (p y).val (p z).val = dist (e y) (e z) := by
  classical
  let sourceMetric : MetricSpace E := H.metric
  have metric_topology_compatibility := H.compatible
  letI : CompactSpace E := H.compact
  have metric_open (V : Set E) (hV : IsOpen V) :
      @IsOpen E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace V := by
    rw [H.compatible]
    exact hV
  letI : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace
    (EuclideanSpace ℝ (Fin 2)) E
  have haOpen : IsOpen (connectedComponent base) := isOpen_connectedComponent
  let A : Type := connectedComponent base
  letI : TopologicalSpace A := inferInstance
  let componentTopology : TopologicalSpace A := inferInstance
  have component_compact : CompactSpace A :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  have component_image_open (U : Set A) (hU : IsOpen U) : IsOpen (Subtype.val '' U : Set E) :=
    haOpen.isOpenEmbedding_subtypeVal.isOpenMap U hU
  have actual_cover_local_hyperbolic_coordinates :
      letI : MetricSpace E := H.metric
      ∀ x : P, ∃ C : SmoothHyperbolicChart E,
        ∃ e : OpenPartialHomeomorph P ℂ,
          x ∈ e.source ∧
          (∀ y ∈ e.source, (p y).val ∈ C.chart.source) ∧
          (∀ y : P, e y = C.chart (p y).val) ∧
          (∀ y ∈ e.source, 0 < (e y).im) := by
    letI : MetricSpace E := H.metric
    have hpTotal : IsLocalHomeomorph (fun y : P => (p y).val) :=
      haOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp hp.isLocalHomeomorph
    intro x
    obtain ⟨L,hxL,hL⟩ := hpTotal x
    obtain ⟨C,hxC⟩ := H.smooth_hyperbolic (p x).val
    let e := L.trans C.chart.toOpenPartialHomeomorph
    have he (y : P) : e y = C.chart (p y).val := by
      change C.chart (L y) = C.chart (p y).val
      rw [← hL]
    have hsource (y : P) (hy : y ∈ e.source) : (p y).val ∈ C.chart.source := by
      have h := hy.2
      change L y ∈ C.chart.source at h
      rwa [← hL] at h
    refine ⟨C,e,?_,hsource,he,?_⟩
    · refine ⟨hxL,?_⟩
      change L x ∈ C.chart.source
      rwa [← hL]
    · intro y hy
      rw [he]
      exact C.upper (p y).val (hsource y hy)
  have actual_cover_coordinate_distance :
      letI : MetricSpace E := H.metric
      ∀ (C : SmoothHyperbolicChart E) (e : OpenPartialHomeomorph P ℂ)
        (hsource : ∀ y ∈ e.source, (p y).val ∈ C.chart.source)
        (he : ∀ y : P, e y = C.chart (p y).val)
        (hupper : ∀ y ∈ e.source, 0 < (e y).im)
        (y z : {w : P // w ∈ e.source}),
        dist (p y.val).val (p z.val).val =
          dist (⟨e y.val,hupper y.val y.property⟩ : H2)
            (⟨e z.val,hupper z.val z.property⟩ : H2) := by
    letI : MetricSpace E := H.metric
    intro C e hsource he hupper y z
    simpa only [he] using C.metric_preserving
      ⟨(p y.val).val,hsource y.val y.property⟩
      ⟨(p z.val).val,hsource z.val z.property⟩
  have actual_cover_overlap_distance :
      letI : MetricSpace E := H.metric
      ∀ (C D : SmoothHyperbolicChart E) (e f : OpenPartialHomeomorph P ℂ)
        (hsource : ∀ y ∈ e.source, (p y).val ∈ C.chart.source)
        (hsource' : ∀ y ∈ f.source, (p y).val ∈ D.chart.source)
        (he : ∀ y : P, e y = C.chart (p y).val)
        (hf : ∀ y : P, f y = D.chart (p y).val)
        (hupper : ∀ y ∈ e.source, 0 < (e y).im)
        (hupper' : ∀ y ∈ f.source, 0 < (f y).im)
        (y z : {w : P // w ∈ e.source ∩ f.source}),
        dist (⟨e y.val,hupper y.val y.property.1⟩ : H2)
            (⟨e z.val,hupper z.val z.property.1⟩ : H2) =
          dist (⟨f y.val,hupper' y.val y.property.2⟩ : H2)
            (⟨f z.val,hupper' z.val z.property.2⟩ : H2) := by
    letI : MetricSpace E := H.metric
    intro C D e f hs hs' he hf hu hu' y z
    exact (actual_cover_coordinate_distance C e hs he hu
      ⟨y.val,y.property.1⟩ ⟨z.val,z.property.1⟩).symm.trans
      (actual_cover_coordinate_distance D f hs' hf hu'
        ⟨y.val,y.property.2⟩ ⟨z.val,z.property.2⟩)
  have actual_cover_upperHalfPlane_charts (x : P) :
      ∃ e : OpenPartialHomeomorph P H2, x ∈ e.source := by
    obtain ⟨C,e,hx,hs,he,hu⟩ := actual_cover_local_hyperbolic_coordinates x
    refine ⟨e.trans UpperHalfPlane.ofComplex,⟨hx,?_⟩⟩
    simp only [Set.mem_preimage,OpenPartialHomeomorph.symm_symm]
    rw [UpperHalfPlane.ofComplex,OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    simpa only [Set.image_univ] using
      (show e x ∈ Set.range ((↑) : H2 → ℂ) from ⟨⟨e x,hu x hx⟩,rfl⟩)
  have actual_projected_path_length {P E : Type} [TopologicalSpace P] [MetricSpace E] (q : P → E) :
      ∃ L : ∀ x y : P, Path x y → ℝ≥0∞,
        (∀ x y (γ : Path x y), L x y γ = eVariationOn (fun t : ℝ => q (γ.extend t)) (Icc 0 1)) ∧
        (∀ x y (γ : Path x y), edist (q x) (q y) ≤ L x y γ) ∧
        (∀ x y (γ : Path x y), L y x γ.symm = L x y γ) ∧
        (∀ x, L x x (Path.refl x) = 0) ∧
        (∀ x y z (γ : Path x y) (δ : Path y z),
          L x z (γ.trans δ) = L x y γ + L y z δ) := by
    let L : ∀ x y : P, Path x y → ℝ≥0∞ :=
      fun _ _ γ => eVariationOn (fun t : ℝ => q (γ.extend t)) (Icc 0 1)
    have image_affine (a b c d : ℝ) (h : 0 < a) :
        (fun t : ℝ => a*t+b) '' Icc c d = Icc (a*c+b) (a*d+b) := by
      ext t
      constructor
      · rintro ⟨s,hs,rfl⟩
        constructor <;> nlinarith [hs.1,hs.2]
      · intro ht
        refine ⟨(t-b)/a,?_,?_⟩
        · constructor
          · apply (le_div_iff₀ h).mpr; nlinarith [ht.1]
          · apply (div_le_iff₀ h).mpr; nlinarith [ht.2]
        · field_simp; ring
    refine ⟨L,fun _ _ _ => rfl,?_,?_,?_,?_⟩
    · intro x y γ
      have h := eVariationOn.edist_le (fun t : ℝ => q (γ.extend t))
        (s := Icc 0 1) (x := 0) (y := 1) (by norm_num) (by norm_num)
      simpa [L] using h
    · intro x y γ
      change eVariationOn (fun t : ℝ => q (γ.symm.extend t)) (Icc 0 1) = _
      simp_rw [Path.extend_symm_apply]
      change eVariationOn ((fun t : ℝ => q (γ.extend t)) ∘ (fun t : ℝ => 1-t)) (Icc 0 1) = _
      rw [eVariationOn.comp_eq_of_antitoneOn _ _ (by intro a ha b hb hab; linarith)]
      have him : (fun t : ℝ => 1-t) '' Icc 0 1 = Icc 0 1 := by
        ext t
        constructor
        · rintro ⟨s,hs,rfl⟩; constructor <;> linarith [hs.1,hs.2]
        · intro ht; refine ⟨1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩; ring
      rw [him]
    · intro x
      apply (eVariationOn.eq_zero_iff _).mpr
      intro s hs t ht
      have hconst (r : ℝ) : (Path.refl x).extend r = x := by
        rfl
      simp only [hconst,edist_self]
    · intro x y z γ δ
      let F : ℝ → E := fun t => q ((γ.trans δ).extend t)
      have hleft : eVariationOn F (Icc 0 (1/2:ℝ)) = L x y γ := by
        have heq : EqOn F ((fun t : ℝ => q (γ.extend t)) ∘ (fun t : ℝ => 2*t)) (Icc 0 (1/2:ℝ)) := by
          intro t ht
          change q ((γ.trans δ).extend t) = q (γ.extend (2*t))
          rw [Path.extend_trans_of_le_half γ δ ht.2]
        rw [eVariationOn.congr heq,
          eVariationOn.comp_eq_of_monotoneOn _ _ (by intro a ha b hb hab; linarith)]
        have him : (fun t : ℝ => 2*t) '' Icc 0 (1/2:ℝ) = Icc 0 1 := by
          convert image_affine 2 0 0 (1/2) (by norm_num) using 1 <;> norm_num
        rw [him]
      have hright : eVariationOn F (Icc (1/2:ℝ) 1) = L y z δ := by
        have heq : EqOn F ((fun t : ℝ => q (δ.extend t)) ∘ (fun t : ℝ => 2*t-1)) (Icc (1/2:ℝ) 1) := by
          intro t ht
          change q ((γ.trans δ).extend t) = q (δ.extend (2*t-1))
          rw [Path.extend_trans_of_half_le γ δ ht.1]
        rw [eVariationOn.congr heq,
          eVariationOn.comp_eq_of_monotoneOn _ _ (by intro a ha b hb hab; linarith)]
        have him : (fun t : ℝ => 2*t-1) '' Icc (1/2:ℝ) 1 = Icc 0 1 := by
          convert image_affine 2 (-1) (1/2) 1 (by norm_num) using 1 <;> norm_num [sub_eq_add_neg]
        rw [him]
      have hadd := eVariationOn.Icc_add_Icc F (s := univ)
        (a := (0:ℝ)) (b := (1/2:ℝ)) (c := (1:ℝ)) (by norm_num) (by norm_num) (mem_univ _)
      simpa only [univ_inter,hleft,hright] using hadd.symm
  have actual_path_infimum_distance {P E : Type} [TopologicalSpace P] [MetricSpace E] (q : P → E)
      (L : ∀ x y : P, Path x y → ℝ≥0∞)
      (hbase : ∀ x y (γ : Path x y), edist (q x) (q y) ≤ L x y γ)
      (hreverse : ∀ x y (γ : Path x y), L y x γ.symm = L x y γ)
      (hzero : ∀ x, L x x (Path.refl x) = 0)
      (hconcat : ∀ x y z (γ : Path x y) (δ : Path y z),
        L x z (γ.trans δ) = L x y γ + L y z δ) :
      ∃ D : P → P → ℝ≥0∞,
        (∀ x y, D x y = ⨅ γ : Path x y, L x y γ) ∧
        (∀ x, D x x = 0) ∧ (∀ x y, D x y = D y x) ∧
        (∀ x y z, D x z ≤ D x y + D y z) ∧
        (∀ x y, edist (q x) (q y) ≤ D x y) := by
    let D : P → P → ℝ≥0∞ := fun x y => ⨅ γ : Path x y, L x y γ
    have hsymm (x y : P) : D x y ≤ D y x := by
      apply le_iInf
      intro γ
      calc
        D x y ≤ L x y γ.symm := iInf_le _ γ.symm
        _ = L y x γ := hreverse y x γ
    refine ⟨D,fun _ _ => rfl,?_,?_,?_,?_⟩
    · intro x
      apply le_antisymm _ bot_le
      exact (iInf_le _ (Path.refl x)).trans_eq (hzero x)
    · intro x y
      exact le_antisymm (hsymm x y) (hsymm y x)
    · intro x y z
      change D x z ≤ (⨅ γ : Path x y, L x y γ) + (⨅ δ : Path y z, L y z δ)
      rw [ENNReal.iInf_add]
      apply le_iInf
      intro γ
      rw [ENNReal.add_iInf]
      apply le_iInf
      intro δ
      exact (iInf_le _ (γ.trans δ)).trans_eq (hconcat x y z γ δ)
    · intro x y
      exact le_iInf (hbase x y)
  have actual_cover_intrinsic_distance :
      letI : MetricSpace E := H.metric
      letI : TopologicalSpace E := H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      ∃ D : P → P → ℝ≥0∞,
        (∀ x y, D x y = ⨅ γ : Path x y,
          eVariationOn (fun t : ℝ => (p (γ.extend t)).val) (Icc 0 1)) ∧
        (∀ x, D x x = 0) ∧ (∀ x y, D x y = D y x) ∧
        (∀ x y z, D x z ≤ D x y + D y z) ∧
        (∀ x y, edist (p x).val (p y).val ≤ D x y) := by
    letI : MetricSpace E := H.metric
    letI : TopologicalSpace E := H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    obtain ⟨L,hL,hbase,hreverse,hzero,hconcat⟩ :=
      actual_projected_path_length (fun y : P => (p y).val)
    obtain ⟨D,hD,hzeroD,hreverseD,htriangleD,hbaseD⟩ :=
      actual_path_infimum_distance (fun y : P => (p y).val) L hbase hreverse hzero hconcat
    refine ⟨D,?_,hzeroD,hreverseD,htriangleD,hbaseD⟩
    intro x y
    rw [hD]
    simp_rw [hL]
  letI : MetricSpace E := H.metric
  letI : TopologicalSpace E := H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨D,hD,hDzero,hDsymm,hDtriangle,hDbase⟩ := actual_cover_intrinsic_distance
  have projected_equality_of_intrinsic_zero (x y : P) (hxy : D x y = 0) : p x = p y := by
    apply Subtype.ext
    apply edist_eq_zero.mp
    exact le_antisymm (hxy ▸ hDbase x y) bot_le
  have intrinsic_separates_distinct_projections (x y : P) (hxy : p x ≠ p y) : D x y ≠ 0 :=
    fun hz => hxy (projected_equality_of_intrinsic_zero x y hz)
  have projected_path_displacement_bound {x y : P} (γ : Path x y) (t : unitInterval) :
      edist (p (γ t)).val (p x).val ≤
        eVariationOn (fun s : ℝ => (p (γ.extend s)).val) (Icc 0 1) := by
    have h := eVariationOn.edist_le (fun s : ℝ => (p (γ.extend s)).val)
      (s := Icc 0 1) (x := t.val) (y := 0) t.property (by norm_num)
    simpa only [Path.extend_extends',Path.extend_zero] using h
  have short_projected_path_stays_in_ball {x y : P} (γ : Path x y) (r : ℝ≥0∞)
      (hshort : eVariationOn (fun s : ℝ => (p (γ.extend s)).val) (Icc 0 1) < r) :
      ∀ t : unitInterval, (p (γ t)).val ∈ Metric.eball (p x).val r := by
    intro t
    exact (projected_path_displacement_bound γ t).trans_lt hshort
  have actual_sheet_path_recovery {P A : Type} [TopologicalSpace P] [TopologicalSpace A]
      (p : P → A) (hp : IsCoveringMap p) (x : P) :
      ∃ U : Set A, p x ∈ U ∧ IsOpen U ∧
        ∀ (y : P) (γ : Path x y), (∀ t, p (γ t) ∈ U) → p x = p y → x = y := by
    obtain ⟨hd,U,hxU,hU,hpU,H,hH⟩ := hp (p x)
    letI := hd
    refine ⟨U,hxU,hU,?_⟩
    intro y γ hr hproj
    let g : unitInterval → p ⁻¹' U := fun t => ⟨γ t,hr t⟩
    have hg : Continuous g := γ.continuous.subtype_mk _
    let label := fun t : unitInterval => (H (g t)).2
    have hl : Continuous label := continuous_snd.comp (H.continuous.comp hg)
    have heq : label 0 = label 1 :=
      (isPreconnected_range hl).subsingleton (mem_range_self 0) (mem_range_self 1)
    have hx : γ 0 = x := γ.source
    have hy : γ 1 = y := γ.target
    have hf : (H (g 0)).1 = (H (g 1)).1 := by
      apply Subtype.ext
      rw [hH,hH]
      change p (γ 0) = p (γ 1)
      rw [hx,hy,hproj]
    have h := congrArg Subtype.val (H.injective (Prod.ext hf heq))
    change γ 0 = γ 1 at h
    rwa [hx,hy] at h
  have intrinsic_zero_implies_equal (x y : P) (hzero : D x y = 0) : x = y := by
    obtain ⟨U,hxU,hU,hrecover⟩ := actual_sheet_path_recovery (A := A) p hp x
    have hUEold := component_image_open U hU
    have hUE : IsOpen (Subtype.val '' U : Set E) := metric_open _ hUEold
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hUE (p x).val ⟨p x,hxU,rfl⟩
    have hsmall : D x y < ENNReal.ofReal r := by
      rw [hzero]
      exact ENNReal.ofReal_pos.mpr hr
    rw [hD] at hsmall
    obtain ⟨γ,hγ⟩ := iInf_lt_iff.mp hsmall
    have hpathU (t : unitInterval) : p (γ t) ∈ U := by
      have ht := short_projected_path_stays_in_ball γ (ENNReal.ofReal r) hγ t
      have hb : (p (γ t)).val ∈ Metric.ball (p x).val r := edist_lt_ofReal.mp ht
      obtain ⟨a,ha,he⟩ := hball hb
      exact (Subtype.ext he : a = p (γ t)) ▸ ha
    exact hrecover y γ hpathU (projected_equality_of_intrinsic_zero x y hzero)
  have strip_boundedVariation (g : ℝ → ℍ) (ε : ℝ) (hε : 0 < ε) (K : NNReal)
      (hg : LipschitzOnWith K (fun t => (g t : ℂ)) (Icc 0 1))
      (hupper : ∀ t ∈ Icc (0 : ℝ) 1, ε ≤ (g t).im) :
      BoundedVariationOn g (Icc 0 1) := by
    have hstrip (z w : ℍ) (hz : ε ≤ z.im) (hw : ε ≤ w.im) :
        dist z w ≤ dist (z : ℂ) (w : ℂ) / ε := by
      have hs : ε ≤ Real.sqrt (z.im * w.im) :=
        Real.le_sqrt_of_sq_le (by
          calc ε ^ 2 = ε * ε := sq ε
               _ ≤ z.im * w.im := mul_le_mul hz hw hε.le z.im_pos.le)
      exact (z.dist_le_dist_coe_div_sqrt w).trans
        (div_le_div_of_nonneg_left dist_nonneg hε hs)
    have hl : LipschitzOnWith (K / (Real.toNNReal ε)) g (Icc 0 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      calc dist (g x) (g y) ≤ dist (g x : ℂ) (g y : ℂ) / ε :=
             hstrip _ _ (hupper x hx) (hupper y hy)
           _ ≤ (K : ℝ) * dist x y / ε :=
             div_le_div_of_nonneg_right (hg.dist_le_mul x hx y hy) hε.le
           _ = ((K / (Real.toNNReal ε) : NNReal) : ℝ) * dist x y := by
             simp only [NNReal.coe_div,Real.coe_toNNReal _ hε.le]
             ring
    simpa only [Function.comp_id] using
      hl.comp_boundedVariationOn (show MapsTo id (Icc (0 : ℝ) 1) (Icc 0 1) from fun _ h => h)
        (BoundedVariationOn.id_Icc 0 1)

  have finite_straight_path (z w : ℍ) : ∃ γ : Path z w,
      BoundedVariationOn γ.extend (Icc 0 1) ∧
        ∀ t : unitInterval, (γ t : ℂ) = AffineMap.lineMap (z : ℂ) (w : ℂ) (t : ℝ) := by
    have hi (t : unitInterval) : 0 < (AffineMap.lineMap (z : ℂ) (w : ℂ) (t : ℝ)).im := by
      simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, UpperHalfPlane.coe_im]
      have hz := z.im_pos
      have hw := w.im_pos
      have h0 := t.property.1
      have h1 := t.property.2
      have hmin := lt_min hz hw
      have hleft := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (min_le_left z.im w.im))
      have hright := mul_nonneg h0 (sub_nonneg.mpr (min_le_right z.im w.im))
      nlinarith
    let γ : Path z w := {
      toFun := fun t => ⟨AffineMap.lineMap (z : ℂ) (w : ℂ) (t : ℝ),hi t⟩
      continuous_toFun := UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
        ((lipschitzWith_lineMap (z : ℂ) (w : ℂ)).continuous.comp continuous_subtype_val)
      source' := by apply UpperHalfPlane.ext; simp
      target' := by apply UpperHalfPlane.ext; simp }
    refine ⟨γ,?_,fun _ => rfl⟩
    have hg : LipschitzOnWith (nndist (z : ℂ) (w : ℂ))
        (fun t => (γ.extend t : ℂ)) (Icc 0 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      simpa only [Path.extend_extends' γ ⟨x,hx⟩,Path.extend_extends' γ ⟨y,hy⟩, γ, Path.coe_mk_mk, UpperHalfPlane.coe_mk] using
        (lipschitzWith_lineMap (z : ℂ) (w : ℂ)).dist_le_mul x y
    apply strip_boundedVariation γ.extend (min z.im w.im) (lt_min z.im_pos w.im_pos) _ hg
    intro t ht
    rw [Path.extend_extends' γ ⟨t,ht⟩]
    change min z.im w.im ≤ (AffineMap.lineMap (z : ℂ) (w : ℂ) t).im
    simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, UpperHalfPlane.coe_im]
    have hz := min_le_left z.im w.im
    have hw := min_le_right z.im w.im
    have h0 := ht.1
    have h1 := ht.2
    have hleft := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hz)
    have hright := mul_nonneg h0 (sub_nonneg.mpr hw)
    nlinarith

  have finite_chart_segment {P E : Type} [TopologicalSpace P] [MetricSpace E]
      (q : P → E) (e : OpenPartialHomeomorph P ℂ)
      (hmetric : ∀ a ∈ e.source, ∀ b ∈ e.source,
        dist (q a) (q b) = dist (UpperHalfPlane.ofComplex (e a)) (UpperHalfPlane.ofComplex (e b)))
      (x y : P) (hx : x ∈ e.source) (hy : y ∈ e.source)
      (hpx : 0 < (e x).im) (hpy : 0 < (e y).im)
      (hseg : ∀ t : unitInterval,
        AffineMap.lineMap (e x) (e y) (t : ℝ) ∈ e.target) :
      ∃ γ : Path x y, BoundedVariationOn (fun t => q (γ.extend t)) (Icc 0 1) := by
    obtain ⟨δ,hδ,hline⟩ := finite_straight_path
      (⟨e x,hpx⟩ : ℍ) (⟨e y,hpy⟩ : ℍ)
    have htarget (t : unitInterval) : (δ t : ℂ) ∈ e.target := by
      rw [hline]
      exact hseg t
    let γ : Path x y := {
      toFun := fun t => e.symm (δ t : ℂ)
      continuous_toFun := e.continuousOn_symm.comp_continuous
        (UpperHalfPlane.continuous_coe.comp δ.continuous) htarget
      source' := by rw [δ.source]; exact e.left_inv hx
      target' := by rw [δ.target]; exact e.left_inv hy }
    have hl : LipschitzOnWith 1 (fun z : ℍ => q (e.symm (z : ℂ)))
        {z : ℍ | (z : ℂ) ∈ e.target} := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [hmetric _ (e.map_target ha) _ (e.map_target hb), e.right_inv ha, e.right_inv hb]
      simp
    have hmap : MapsTo δ.extend (Icc 0 1) {z : ℍ | (z : ℂ) ∈ e.target} := by
      intro t ht
      rw [Path.extend_extends' δ ⟨t,ht⟩]
      exact htarget ⟨t,ht⟩
    refine ⟨γ,?_⟩
    exact hl.comp_boundedVariationOn hmap hδ
  let actualCoverEMetric : EMetricSpace P :=
    { PseudoEMetricSpace.ofEDist D hDzero hDsymm hDtriangle with
      eq_of_edist_eq_zero := fun {x y} h => intrinsic_zero_implies_equal x y h }
  have actualCoverEMetric_edist (x y : P) :
      @edist P actualCoverEMetric.toEDist x y = D x y := rfl
  have locally_finite_projected_paths (x : P) :
      ∃ U : Set P, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
        ∃ γ : Path x y,
          BoundedVariationOn (fun t => (p (γ.extend t)).val) (Icc 0 1) := by
    obtain ⟨C,e,hx,hs,he,hu⟩ := actual_cover_local_hyperbolic_coordinates x
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
    let U := e.source ∩ e ⁻¹' Metric.ball (e x) r
    have hopen : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
    have hcenter : e x ∈ Metric.ball (e x) r := Metric.mem_ball_self hr
    refine ⟨U,hopen,⟨hx,hcenter⟩,?_⟩
    intro y hy
    have hmetric : ∀ a ∈ e.source, ∀ b ∈ e.source,
        dist (p a).val (p b).val =
          dist (UpperHalfPlane.ofComplex (e a)) (UpperHalfPlane.ofComplex (e b)) := by
      intro a ha b hb
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hu a ha),
        UpperHalfPlane.ofComplex_apply_of_im_pos (hu b hb)]
      exact actual_cover_coordinate_distance C e hs he hu ⟨a,ha⟩ ⟨b,hb⟩
    apply finite_chart_segment (fun z => (p z).val) e hmetric x y hx hy.1 (hu x hx) (hu y hy.1)
    intro t
    exact hball ((convex_ball (e x) r).segment_subset hcenter hy.2
      (lineMap_mem_segment ℝ (e x) (e y) t.property))
  have locally_finite_distance (x : P) :
      ∃ U : Set P, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, D x y ≠ ⊤ := by
    obtain ⟨U,hU,hx,hpaths⟩ := locally_finite_projected_paths x
    refine ⟨U,hU,hx,?_⟩
    intro y hy
    obtain ⟨γ,hγ⟩ := hpaths y hy
    apply ne_top_of_le_ne_top hγ
    rw [hD]
    exact iInf_le _ γ
  have actual_intrinsic_distance_finite (x y : P) : D x y ≠ ⊤ := by
    let R : Set P := {z | D x z ≠ ⊤}
    have hopen : IsOpen R := by
      apply isOpen_iff_forall_mem_open.mpr
      intro z hz
      obtain ⟨U,hU,hzU,hfinite⟩ := locally_finite_distance z
      refine ⟨U,?_,hU,hzU⟩
      intro w hw
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hz,hfinite w hw⟩)
        (hDtriangle x z w)
    have hclosed : IsClosed R := by
      apply isOpen_compl_iff.mp
      apply isOpen_iff_forall_mem_open.mpr
      intro z hz
      obtain ⟨U,hU,hzU,hfinite⟩ := locally_finite_distance z
      refine ⟨U,?_,hU,hzU⟩
      intro w hw hfin
      apply hz
      exact ne_top_of_le_ne_top
        (ENNReal.add_ne_top.mpr ⟨hfin,by rw [hDsymm];exact hfinite w hw⟩)
        (hDtriangle x w z)
    have hRuniv : R = univ := (show IsClopen R from ⟨hclosed,hopen⟩).eq_univ
      ⟨x,by change D x x ≠ ⊤;rw [hDzero];exact ENNReal.zero_ne_top⟩
    have hy : y ∈ R := hRuniv ▸ mem_univ y
    exact hy
  let actualCoverMetric : MetricSpace P :=
    @EMetricSpace.toMetricSpace P actualCoverEMetric actual_intrinsic_distance_finite
  have actualCoverMetric_dist (x y : P) :
      @dist P actualCoverMetric.toDist x y = (D x y).toReal := rfl
  have strip_variation_bound (g : ℝ → ℍ) (ε : ℝ) (hε : 0 < ε) (K : NNReal)
      (hg : LipschitzOnWith K (fun t => (g t : ℂ)) (Icc 0 1))
      (hupper : ∀ t ∈ Icc (0 : ℝ) 1, ε ≤ (g t).im) :
      eVariationOn g (Icc 0 1) ≤ (K / Real.toNNReal ε : NNReal) := by
    have hstrip (z w : ℍ) (hz : ε ≤ z.im) (hw : ε ≤ w.im) :
        dist z w ≤ dist (z : ℂ) (w : ℂ) / ε := by
      have hs : ε ≤ Real.sqrt (z.im * w.im) :=
        Real.le_sqrt_of_sq_le (by
          calc ε ^ 2 = ε * ε := sq ε
               _ ≤ z.im * w.im := mul_le_mul hz hw hε.le z.im_pos.le)
      exact (z.dist_le_dist_coe_div_sqrt w).trans
        (div_le_div_of_nonneg_left dist_nonneg hε hs)
    have hl : LipschitzOnWith (K / (Real.toNNReal ε)) g (Icc 0 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      calc dist (g x) (g y) ≤ dist (g x : ℂ) (g y : ℂ) / ε :=
             hstrip _ _ (hupper x hx) (hupper y hy)
           _ ≤ (K : ℝ) * dist x y / ε :=
             div_le_div_of_nonneg_right (hg.dist_le_mul x hx y hy) hε.le
           _ = ((K / (Real.toNNReal ε) : NNReal) : ℝ) * dist x y := by
             simp only [NNReal.coe_div,Real.coe_toNNReal _ hε.le]
             ring
    have hb := hl.comp_eVariationOn_le
      (show MapsTo id (Icc (0 : ℝ) 1) (Icc 0 1) from fun _ h => h)
    simpa only [Function.comp_id,eVariationOn_id_Icc,sub_zero,ENNReal.ofReal_one,mul_one] using hb

  have finite_chart_segment_bound {P E : Type} [TopologicalSpace P] [MetricSpace E]
      (q : P → E) (e : OpenPartialHomeomorph P ℂ)
      (hmetric : ∀ a ∈ e.source, ∀ b ∈ e.source,
        dist (q a) (q b) = dist (UpperHalfPlane.ofComplex (e a)) (UpperHalfPlane.ofComplex (e b)))
      (x y : P) (hx : x ∈ e.source) (hy : y ∈ e.source)
      (hpx : 0 < (e x).im) (hpy : 0 < (e y).im)
      (hseg : ∀ t : unitInterval,
        AffineMap.lineMap (e x) (e y) (t : ℝ) ∈ e.target) :
      ∃ γ : Path x y, eVariationOn (fun t => q (γ.extend t)) (Icc 0 1) ≤
        (nndist (e x) (e y) / Real.toNNReal (min (e x).im (e y).im) : NNReal) := by
    obtain ⟨δ,hδ,hline⟩ := finite_straight_path
      (⟨e x,hpx⟩ : ℍ) (⟨e y,hpy⟩ : ℍ)
    have htarget (t : unitInterval) : (δ t : ℂ) ∈ e.target := by
      rw [hline]
      exact hseg t
    let γ : Path x y := {
      toFun := fun t => e.symm (δ t : ℂ)
      continuous_toFun := e.continuousOn_symm.comp_continuous
        (UpperHalfPlane.continuous_coe.comp δ.continuous) htarget
      source' := by rw [δ.source]; exact e.left_inv hx
      target' := by rw [δ.target]; exact e.left_inv hy }
    have hl : LipschitzOnWith 1 (fun z : ℍ => q (e.symm (z : ℂ)))
        {z : ℍ | (z : ℂ) ∈ e.target} := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [hmetric _ (e.map_target ha) _ (e.map_target hb), e.right_inv ha, e.right_inv hb]
      simp
    have hmap : MapsTo δ.extend (Icc 0 1) {z : ℍ | (z : ℂ) ∈ e.target} := by
      intro t ht
      rw [Path.extend_extends' δ ⟨t,ht⟩]
      exact htarget ⟨t,ht⟩
    have hg : LipschitzOnWith (nndist (e x) (e y))
        (fun t => (δ.extend t : ℂ)) (Icc 0 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      simpa only [Path.extend_extends' δ ⟨a,ha⟩,Path.extend_extends' δ ⟨b,hb⟩,hline] using
        (lipschitzWith_lineMap (e x) (e y)).dist_le_mul a b
    have hupper (t : ℝ) (ht : t ∈ Icc 0 1) :
        min (e x).im (e y).im ≤ (δ.extend t).im := by
      rw [Path.extend_extends' δ ⟨t,ht⟩]
      change min (e x).im (e y).im ≤ (δ ⟨t,ht⟩ : ℂ).im
      rw [hline]
      simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.real_smul,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,zero_mul,add_zero]
      have hleft := mul_nonneg (sub_nonneg.mpr ht.2)
        (sub_nonneg.mpr (min_le_left (e x).im (e y).im))
      have hright := mul_nonneg ht.1
        (sub_nonneg.mpr (min_le_right (e x).im (e y).im))
      nlinarith
    have hbound := strip_variation_bound δ.extend (min (e x).im (e y).im)
      (lt_min hpx hpy) _ hg hupper
    refine ⟨γ,?_⟩
    calc _ ≤ eVariationOn δ.extend (Icc 0 1) := by
           have heq : EqOn (fun t => q (γ.extend t))
               ((fun z : ℍ => q (e.symm (z : ℂ))) ∘ δ.extend) (Icc 0 1) := by
             intro t ht
             change q (γ.extend t) = q (e.symm (δ.extend t : ℂ))
             rw [Path.extend_apply γ ht]
             simp only [Function.comp_apply,Path.extend_apply δ ht]
             rfl
           rw [eVariationOn.congr heq]
           simpa only [ENNReal.coe_one,one_mul] using hl.comp_eVariationOn_le hmap
         _ ≤ _ := hbound
  have locally_controlled_intrinsic_distance (x : P) :
      ∃ (e : OpenPartialHomeomorph P ℂ) (U : Set P),
        IsOpen U ∧ x ∈ U ∧ U ⊆ e.source ∧
          0 < (e x).im ∧ ∀ y ∈ U,
            D x y ≤ (nndist (e x) (e y) /
              Real.toNNReal (min (e x).im (e y).im) : NNReal) := by
    obtain ⟨C,e,hx,hs,he,hu⟩ := actual_cover_local_hyperbolic_coordinates x
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
    let U := e.source ∩ e ⁻¹' Metric.ball (e x) r
    have hopen : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
    have hcenter : e x ∈ Metric.ball (e x) r := Metric.mem_ball_self hr
    refine ⟨e,U,hopen,⟨hx,hcenter⟩,fun _ hy => hy.1,hu x hx,?_⟩
    intro y hy
    have hmetric : ∀ a ∈ e.source, ∀ b ∈ e.source,
        dist (p a).val (p b).val =
          dist (UpperHalfPlane.ofComplex (e a)) (UpperHalfPlane.ofComplex (e b)) := by
      intro a ha b hb
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hu a ha),
        UpperHalfPlane.ofComplex_apply_of_im_pos (hu b hb)]
      exact actual_cover_coordinate_distance C e hs he hu ⟨a,ha⟩ ⟨b,hb⟩
    have hseg (t : unitInterval) :
        AffineMap.lineMap (e x) (e y) (t : ℝ) ∈ e.target :=
      hball ((convex_ball (e x) r).segment_subset hcenter hy.2
        (lineMap_mem_segment ℝ (e x) (e y) t.property))
    obtain ⟨γ,hγ⟩ := finite_chart_segment_bound (fun z => (p z).val) e hmetric
      x y hx hy.1 (hu x hx) (hu y hy.1) hseg
    rw [hD]
    exact (iInf_le _ γ).trans hγ
  have intrinsic_distance_tendsto_zero (x : P) :
      Tendsto (fun y => D x y) (𝓝 x) (𝓝 0) := by
    obtain ⟨e,U,hU,hx,hsource,hpos,hbound⟩ := locally_controlled_intrinsic_distance x
    have hecont : ContinuousAt e x := e.continuousAt (hsource hx)
    have him : ContinuousAt (fun y => (e y).im) x :=
      Complex.continuous_im.continuousAt.comp hecont
    have hden : ContinuousAt (fun y => Real.toNNReal (min (e x).im (e y).im)) x :=
      continuous_real_toNNReal.continuousAt.comp (continuousAt_const.min him)
    have hden0 : Real.toNNReal (min (e x).im (e x).im) ≠ 0 := by
      simp only [min_self]
      exact ne_of_gt (Real.toNNReal_pos.mpr hpos)
    have hnum : ContinuousAt (fun y => nndist (e x) (e y)) x :=
      continuousAt_const.nndist hecont
    have hratio : ContinuousAt (fun y =>
        ((nndist (e x) (e y) / Real.toNNReal (min (e x).im (e y).im) : NNReal) : ℝ≥0∞)) x :=
      ENNReal.continuous_coe.continuousAt.comp (hnum.div hden hden0)
    have hrzero : Tendsto (fun y =>
        ((nndist (e x) (e y) / Real.toNNReal (min (e x).im (e y).im) : NNReal) : ℝ≥0∞))
        (𝓝 x) (𝓝 0) := by simpa only [nndist_self,zero_div,ENNReal.coe_zero] using hratio.tendsto
    exact Filter.Tendsto.squeeze' tendsto_const_nhds hrzero
      (Eventually.of_forall fun y => bot_le)
      (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hbound y hy)
  have intrinsic_metric_identity_continuous :
      @Continuous P P (inferInstance : TopologicalSpace P)
        actualCoverMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace id := by
    apply (@continuous_iff_continuousAt P P (inferInstance : TopologicalSpace P)
      actualCoverMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace id).mpr
    intro x
    apply (@EMetric.tendsto_nhds P P
      actualCoverMetric.toPseudoMetricSpace.toPseudoEMetricSpace (𝓝 x) id x).mpr
    intro ε hε
    have hs := (intrinsic_distance_tendsto_zero x).eventually (eventually_lt_nhds hε)
    filter_upwards [hs] with y hy
    change D y x < ε
    rwa [hDsymm]
  have actual_sheet_neighborhood_control {P A : Type} [TopologicalSpace P] [TopologicalSpace A]
      (p : P → A) (hp : IsCoveringMap p) (x : P)
      (V : Set P) (hV : IsOpen V) (hxV : x ∈ V) :
      ∃ W : Set A, IsOpen W ∧ p x ∈ W ∧
        ∀ (y : P) (γ : Path x y), (∀ t, p (γ t) ∈ W) → y ∈ V := by
    classical
    obtain ⟨hd,U,hxU,hU,hpU,H,hH⟩ := hp (p x)
    letI := hd
    let k := (H ⟨x,hxU⟩).2
    let s : U → P := fun a => (H.symm (a,k)).val
    have hs : Continuous s := continuous_subtype_val.comp
      (H.symm.continuous.comp (continuous_id.prodMk continuous_const))
    have hsx : s ⟨p x,hxU⟩ = x := by
      have hc : H ⟨x,hxU⟩ = (⟨p x,hxU⟩,k) :=
        Prod.ext (Subtype.ext (hH _)) rfl
      change (H.symm (⟨p x,hxU⟩,k)).val = x
      rw [←hc,H.symm_apply_apply]
    let W : Set A := Subtype.val '' (s ⁻¹' V)
    have hW : IsOpen W := hU.isOpenEmbedding_subtypeVal.isOpenMap _ (hV.preimage hs)
    have hxW : p x ∈ W := ⟨⟨p x,hxU⟩,by change s ⟨p x,hxU⟩ ∈ V; rwa [hsx],rfl⟩
    have hWU : W ⊆ U := by rintro _ ⟨a,_,rfl⟩;exact a.property
    refine ⟨W,hW,hxW,?_⟩
    intro y γ hpath
    let g : unitInterval → p ⁻¹' U := fun t => ⟨γ t,hWU (hpath t)⟩
    have hg : Continuous g := γ.continuous.subtype_mk _
    let label := fun t : unitInterval => (H (g t)).2
    have hl : Continuous label := continuous_snd.comp (H.continuous.comp hg)
    have heq : label 0 = label 1 :=
      (isPreconnected_range hl).subsingleton (mem_range_self 0) (mem_range_self 1)
    obtain ⟨a,ha,haeq⟩ := hpath 1
    have haeq' : a.val = p y := by simpa only [γ.target] using haeq
    have hcoords : H ⟨y,hWU (by simpa only [γ.target] using hpath 1)⟩ = (a,k) := by
      apply Prod.ext
      · apply Subtype.ext
        rw [hH]
        exact haeq'.symm
      · have hyend : g 1 = ⟨y,hWU (by simpa only [γ.target] using hpath 1)⟩ :=
          Subtype.ext γ.target
        change (H ⟨y,_⟩).2 = k
        rw [←hyend]
        change label 1 = k
        rw [←heq]
        change (H ⟨γ 0,_⟩).2 = (H ⟨x,hxU⟩).2
        exact congrArg (fun a : p ⁻¹' U => (H a).2) (Subtype.ext γ.source)
    have hy : s a = y := by
      change (H.symm (a,k)).val = y
      rw [←hcoords,H.symm_apply_apply]
    rwa [←hy]
  have intrinsic_ball_subset_original_neighborhood (x : P) (V : Set P)
      (hV : IsOpen V) (hxV : x ∈ V) :
      ∃ r : ℝ, 0 < r ∧ ∀ y, D x y < ENNReal.ofReal r → y ∈ V := by
    obtain ⟨W,hW,hxW,hcontrol⟩ := actual_sheet_neighborhood_control (A := A) p hp x V hV hxV
    have hWE : IsOpen (Subtype.val '' W : Set E) := metric_open _ (component_image_open W hW)
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hWE (p x).val ⟨p x,hxW,rfl⟩
    refine ⟨r,hr,?_⟩
    intro y hdist
    rw [hD] at hdist
    obtain ⟨γ,hγ⟩ := iInf_lt_iff.mp hdist
    apply hcontrol y γ
    intro t
    have ht := short_projected_path_stays_in_ball γ (ENNReal.ofReal r) hγ t
    have hb : (p (γ t)).val ∈ Metric.ball (p x).val r := edist_lt_ofReal.mp ht
    obtain ⟨a,ha,he⟩ := hball hb
    exact (Subtype.ext he : a = p (γ t)) ▸ ha
  have reverse_intrinsic_metric_identity_continuous :
      @Continuous P P actualCoverMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (inferInstance : TopologicalSpace P) id := by
    apply (@continuous_def P P actualCoverMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (inferInstance : TopologicalSpace P) id).mpr
    intro V hV
    apply (@Metric.isOpen_iff P actualCoverMetric.toPseudoMetricSpace V).mpr
    intro x hx
    obtain ⟨r,hr,hball⟩ := intrinsic_ball_subset_original_neighborhood x V hV hx
    refine ⟨r,hr,?_⟩
    intro y hy
    apply hball y
    have hdist := (@edist_lt_ofReal P actualCoverMetric.toPseudoMetricSpace y x r).mpr hy
    change D y x < ENNReal.ofReal r at hdist
    rwa [hDsymm]
  have actualCoverMetric_topology :
      actualCoverMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace P) := by
    apply le_antisymm
    · exact (@continuous_id_iff_le P
        actualCoverMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (inferInstance : TopologicalSpace P)).mp reverse_intrinsic_metric_identity_continuous
    · exact (@continuous_id_iff_le P (inferInstance : TopologicalSpace P)
        actualCoverMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace).mp
        intrinsic_metric_identity_continuous
  let actualBaseMetric : MetricSpace A :=
    MetricSpace.induced (Subtype.val : A → E) Subtype.val_injective sourceMetric
  have actualBaseMetric_topology :
      actualBaseMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace A) := by
    exact congrArg (fun t : TopologicalSpace E =>
      TopologicalSpace.induced (Subtype.val : A → E) t) metric_topology_compatibility
  let baseMetricCompatible := @MetricSpace.replaceTopology A componentTopology
    actualBaseMetric actualBaseMetric_topology.symm
  letI : MetricSpace A := baseMetricCompatible
  letI : PseudoMetricSpace A := baseMetricCompatible.toPseudoMetricSpace
  letI : UniformSpace A := baseMetricCompatible.toPseudoMetricSpace.toUniformSpace
  letI : MetricSpace P := actualCoverMetric.replaceTopology actualCoverMetric_topology.symm
  letI : CompactSpace A := component_compact
  let actualProjection : P → A := p
  letI : CompleteSpace A := complete_of_compact
  have actual_base_projection_lipschitz : LipschitzWith 1 actualProjection := by
    apply LipschitzWith.of_edist_le
    intro x y
    change edist (p x).val (p y).val ≤ D x y
    exact hDbase x y
  have projected_cauchy_sequences_converge (u : ℕ → P) (hu : CauchySeq u) :
      ∃ a : A, Tendsto (fun n => actualProjection (u n)) atTop (𝓝 a) := by
    have hproj : CauchySeq (fun n => actualProjection (u n)) := by
      apply EMetric.cauchySeq_iff.mpr
      intro ε hε
      obtain ⟨N,hN⟩ := EMetric.cauchySeq_iff.mp hu ε hε
      refine ⟨N,?_⟩
      intro m hm n hn
      exact (hDbase (u m) (u n)).trans_lt (hN m hm n hn)
    exact cauchySeq_tendsto_of_complete hproj
  have cauchy_tail_projected_paths (u : ℕ → P) (hu : CauchySeq u)
      (a : A) (ha : Tendsto (fun n => actualProjection (u n)) atTop (𝓝 a))
      (U : Set A) (hU : IsOpen U) (haU : a ∈ U) :
      ∃ N : ℕ, ∀ n ≥ N, ∃ γ : Path (u N) (u n),
        ∀ t, actualProjection (γ t) ∈ U := by
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU a haU
    have hnear := Metric.tendsto_nhds.mp ha (r / 4) (by positivity)
    obtain ⟨N0,hN0⟩ := Filter.eventually_atTop.mp hnear
    obtain ⟨N1,hN1⟩ := Metric.cauchySeq_iff.mp hu (r / 4) (by positivity)
    let N := max N0 N1
    have hN0' : N0 ≤ N := le_max_left _ _
    have hN1' : N1 ≤ N := le_max_right _ _
    have hbase : dist (actualProjection (u N)) a < r / 4 := hN0 N hN0'
    refine ⟨N,?_⟩
    intro n hn
    have hdist : dist (u N) (u n) < r / 2 :=
      (hN1 N hN1' n (hN1'.trans hn)).trans (by linarith)
    have hsmall : D (u N) (u n) < ENNReal.ofReal (r / 2) := by
      exact edist_lt_ofReal.mpr hdist
    rw [hD] at hsmall
    obtain ⟨γ,hγ⟩ := iInf_lt_iff.mp hsmall
    refine ⟨γ,?_⟩
    intro t
    have hstep : dist (actualProjection (γ t)) (actualProjection (u N)) < r / 2 := by
      apply edist_lt_ofReal.mp
      exact short_projected_path_stays_in_ball γ (ENNReal.ofReal (r / 2)) hγ t
    apply hball
    change dist (actualProjection (γ t)) a < r
    have htri := dist_triangle (actualProjection (γ t)) (actualProjection (u N)) a
    linarith
  have actual_cover_cauchy_sequence_converges (u : ℕ → P) (hu : CauchySeq u) :
      ∃ b : P, Tendsto u atTop (𝓝 b) := by
    obtain ⟨a,ha⟩ := projected_cauchy_sequences_converge u hu
    have hpc : IsCoveringMap actualProjection := hp
    obtain ⟨hd,U,haU,hU,hpU,H,hH⟩ := hpc a
    letI := hd
    obtain ⟨N,hpaths⟩ := cauchy_tail_projected_paths u hu a ha U hU haU
    have hnU (n : ℕ) : actualProjection (u (n + N)) ∈ U := by
      obtain ⟨γ,hγ⟩ := hpaths (n + N) (Nat.le_add_left N n)
      simpa only [γ.target] using hγ 1
    let v : ℕ → actualProjection ⁻¹' U := fun n => ⟨u (n + N),hnU n⟩
    let k := (H (v 0)).2
    have hlabel (n : ℕ) : (H (v n)).2 = k := by
      obtain ⟨γ,hγ⟩ := hpaths (n + N) (Nat.le_add_left N n)
      let g : unitInterval → actualProjection ⁻¹' U := fun t => ⟨γ t,hγ t⟩
      have hg : Continuous g := γ.continuous.subtype_mk _
      have hc : Continuous (fun t => (H (g t)).2) :=
        continuous_snd.comp (H.continuous.comp hg)
      have heq := (isPreconnected_range hc).subsingleton (mem_range_self 0) (mem_range_self 1)
      have h0 : g 0 = v 0 := Subtype.ext (by simpa only [v,Nat.zero_add] using γ.source)
      have h1 : g 1 = v n := Subtype.ext γ.target
      change (H (g 0)).2 = (H (g 1)).2 at heq
      rw [h0,h1] at heq
      exact heq.symm
    have hbase : Tendsto (fun n => (H (v n)).1) atTop (𝓝 (⟨a,haU⟩ : U)) := by
      apply tendsto_subtype_rng.mpr
      simpa only [hH,v,Function.comp_def] using ha.comp (tendsto_add_atTop_nat N)
    have hcoords : Tendsto (fun n => H (v n)) atTop (𝓝 (⟨a,haU⟩,k)) := by
      have hk : Tendsto (fun _ : ℕ => k) atTop (𝓝 k) := tendsto_const_nhds
      have hc : Tendsto (fun n => ((H (v n)).1,k)) atTop (𝓝 (⟨a,haU⟩,k)) :=
        hbase.prodMk_nhds hk
      exact hc.congr' (Eventually.of_forall fun n =>
        (show ((H (v n)).1,k) = H (v n) from Prod.ext rfl (hlabel n).symm))
    have hlimit := ((continuous_subtype_val.comp H.symm.continuous).tendsto
      (⟨a,haU⟩,k)).comp hcoords
    refine ⟨(H.symm (⟨a,haU⟩,k)).val,?_⟩
    apply (tendsto_add_atTop_iff_nat N).mp
    simpa only [Function.comp_def,v,Homeomorph.symm_apply_apply] using hlimit
  have actual_cover_complete : CompleteSpace P :=
    Metric.complete_of_cauchySeq_tendsto actual_cover_cauchy_sequence_converges
  have actual_hyperbolic_metric_charts (x : P) :
      ∃ e : OpenPartialHomeomorph P H2, x ∈ e.source ∧
        ∀ y ∈ e.source, ∀ z ∈ e.source,
          dist (actualProjection y) (actualProjection z) = dist (e y) (e z) := by
    obtain ⟨C,e,hx,hs,he,hu⟩ := actual_cover_local_hyperbolic_coordinates x
    let f := e.trans UpperHalfPlane.ofComplex
    have hxF : x ∈ f.source := by
      refine ⟨hx,?_⟩
      simp only [Set.mem_preimage,OpenPartialHomeomorph.symm_symm]
      rw [UpperHalfPlane.ofComplex,OpenPartialHomeomorph.symm_source,
        Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
      simpa only [Set.image_univ] using
        (show e x ∈ Set.range ((↑) : H2 → ℂ) from ⟨⟨e x,hu x hx⟩,rfl⟩)
    refine ⟨f,hxF,?_⟩
    intro y hy z hz
    change dist (p y).val (p z).val =
      dist (UpperHalfPlane.ofComplex (e y)) (UpperHalfPlane.ofComplex (e z))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hu y hy.1),
      UpperHalfPlane.ofComplex_apply_of_im_pos (hu z hz.1)]
    exact actual_cover_coordinate_distance C e hs he hu ⟨y,hy.1⟩ ⟨z,hz.1⟩
  have actual_hyperbolic_transition_isometry
      (e f : OpenPartialHomeomorph P H2)
      (he : ∀ y ∈ e.source, ∀ z ∈ e.source,
        dist (actualProjection y) (actualProjection z) = dist (e y) (e z))
      (hf : ∀ y ∈ f.source, ∀ z ∈ f.source,
        dist (actualProjection y) (actualProjection z) = dist (f y) (f z)) :
      Isometry (fun z : (e.symm.trans f).source => (e.symm.trans f) z.val) := by
    apply Isometry.of_dist_eq
    intro y z
    have hye : e.symm y.val ∈ e.source := e.map_target y.property.1
    have hze : e.symm z.val ∈ e.source := e.map_target z.property.1
    have hyf : e.symm y.val ∈ f.source := y.property.2
    have hzf : e.symm z.val ∈ f.source := z.property.2
    change dist (f (e.symm y.val)) (f (e.symm z.val)) = dist y.val z.val
    rw [←hf _ hyf _ hzf,he _ hye _ hze,e.right_inv y.property.1,e.right_inv z.property.1]
  have zero_eq_I : verticalPath 0 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [verticalPath]
  have vertical_radius_sphere (r : ℝ) (hr : 0 ≤ r) (z : H2)
      (h : dist UpperHalfPlane.I z = r) :
      Real.exp r * (z.re ^ 2 + z.im ^ 2 + 1) =
        z.im * (1 + (Real.exp r) ^ 2) := by
    have hstd : dist (verticalPath 0) (verticalPath r) = r := by
      simpa [Real.dist_eq,abs_of_nonneg hr,abs_of_nonpos (neg_nonpos.mpr hr)] using
        verticalPath_isometry.dist_eq 0 r
    have hc := congrArg Real.cosh (h.trans (zero_eq_I ▸ hstd).symm)
    rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
    simp only [verticalPath,UpperHalfPlane.mk_re,UpperHalfPlane.mk_im] at hc
    simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,zero_sub,neg_sq,
      one_pow,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hc
    field_simp at hc
    nlinarith [hc]
  have denominator_nonzero (a b : ℝ) (hab : 0 < a^2+b^2) (w : H2) :
      (-(b : ℂ) * (w : ℂ) + a) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [Complex.mul_im] at him
    have hb : b = 0 := by
      rcases him with hb | hw
      · exact hb
      · exact (w.im_pos.ne' hw).elim
    have ha : a ≠ 0 := by
      intro ha
      rw [ha,hb] at hab
      norm_num at hab
    exact ha (by simpa [hb] using h)
  have rotation_maps_vertical_radius (r : ℝ) (hr : 0 ≤ r) (z : H2)
      (h : dist UpperHalfPlane.I z = r)
      (hab : 0 < (1-Real.exp r*z.im)^2+z.re^2) :
      (stabilizerRotation (1-Real.exp r*z.im) z.re hab • verticalPath r : H2) = z := by
    let a := 1-Real.exp r*z.im
    let b := z.re
    have hsphere := vertical_radius_sphere r hr z h
    have hEim : (Complex.exp (r : ℂ)).im = 0 := by
      simpa using Complex.exp_ofReal_im r
    have hEre : (Complex.exp (r : ℂ)).re = Real.exp r := by
      simpa using Complex.exp_ofReal_re r
    apply UpperHalfPlane.coe_injective
    rw [stabilizerRotation_coe_smul]
    apply (div_eq_iff (denominator_nonzero a b hab (verticalPath r))).2
    apply Complex.ext
    · simp [verticalPath,Complex.add_re,Complex.mul_re,Complex.neg_re,
        Complex.mul_im,Complex.neg_im]
      try rw [hEim]
      dsimp [a,b]
      ring
    · simp [verticalPath,Complex.add_im,Complex.mul_im,Complex.neg_im,
        Complex.mul_re,Complex.neg_re]
      try rw [hEre]
      dsimp [a,b]
      nlinarith [hsphere]
  have exists_stabilizer_radius (r : ℝ) (hr : 0 ≤ r) (z : H2) (h : dist UpperHalfPlane.I z = r) :
      ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = UpperHalfPlane.I ∧ e (verticalPath r) = z := by
    let a : ℝ := 1-Real.exp r*z.im
    let b : ℝ := z.re
    by_cases hpole : a = 0 ∧ b = 0
    · have him : z.im = Real.exp (-r) := by
        have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
        have ha : Real.exp r * z.im = 1 := by dsimp [a] at hpole;linarith [hpole.1]
        rw [Real.exp_neg,←one_div]
        exact (eq_div_iff he).2 (by simpa [mul_comm] using ha)
      have hz : z = verticalPath (-r) := by
        apply UpperHalfPlane.ext_re_im
        · simpa [verticalPath,b] using hpole.2
        · simpa [verticalPath] using him
      refine ⟨IsometryEquiv.constSMul
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S),?_,?_⟩
      · rw [←zero_eq_I]
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath 0
        have hh := modular_S_verticalPath 0
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath 0 : H2) = verticalPath (-0) at hh
        simpa only [neg_zero] using hh
      · rw [hz]
        change (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • verticalPath r : H2) = verticalPath (-r)
        exact modular_S_verticalPath r
    · have hab : 0 < a^2+b^2 := by
        by_contra hn
        have ha : a = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
        have hb : b = 0 := by nlinarith [sq_nonneg a,sq_nonneg b]
        exact hpole ⟨ha,hb⟩
      refine ⟨IsometryEquiv.constSMul (stabilizerRotation a b hab),?_,?_⟩
      · exact stabilizerRotation_fixes_I a b hab
      · exact rotation_maps_vertical_radius r hr z h hab
  have ordered_pair_alignment (x y : H2) :
      ∃ e : H2 ≃ᵢ H2, e UpperHalfPlane.I = x ∧ e (verticalPath (dist x y)) = y := by
    let e0 : H2 ≃ᵢ H2 := IsometryEquiv.constSMul x.toSL2R
    have he0 : e0 UpperHalfPlane.I = x := x.toSL2R_smul_I
    let w := e0.symm y
    have hw : dist UpperHalfPlane.I w = dist x y := by
      have hd := e0.isometry.dist_eq UpperHalfPlane.I (e0.symm y)
      rw [e0.apply_symm_apply,he0] at hd
      exact hd.symm
    obtain ⟨s,hs0,hsr⟩ := exists_stabilizer_radius (dist x y) dist_nonneg w hw
    refine ⟨s.trans e0,?_,?_⟩
    · rw [IsometryEquiv.trans_apply,hs0,he0]
    · rw [IsometryEquiv.trans_apply,hsr]
      exact e0.apply_symm_apply y
  have actual_segment (x y : H2) :
      ∃ γ : Path x y, ∀ s t : unitInterval,
        dist (γ s) (γ t) = dist x y * dist (s : ℝ) (t : ℝ) := by
    obtain ⟨e,he0,he1⟩ := ordered_pair_alignment x y
    let γ : Path x y := {
      toFun := fun t => e (verticalPath ((t : ℝ) * dist x y))
      continuous_toFun := e.continuous.comp
        (verticalPath_isometry.continuous.comp (continuous_subtype_val.mul continuous_const))
      source' := by
        change e (verticalPath (0 * dist x y)) = x
        simpa only [zero_mul,zero_eq_I] using he0
      target' := by
        change e (verticalPath (1 * dist x y)) = y
        simpa only [one_mul] using he1 }
    refine ⟨γ,?_⟩
    intro s t
    change dist (e (verticalPath ((s : ℝ)*dist x y)))
      (e (verticalPath ((t : ℝ)*dist x y))) = _
    rw [e.isometry.dist_eq,verticalPath_isometry.dist_eq,Real.dist_eq,Real.dist_eq,
      ←sub_mul,abs_mul,abs_of_nonneg (dist_nonneg (x := x) (y := y)),mul_comm]
  have exact_geodesic_segment (x y : H2) : ∃ γ : Path x y,
      eVariationOn γ.extend (Icc 0 1) = ENNReal.ofReal (dist x y) ∧
        ∀ t : unitInterval, dist x (γ t) ≤ dist x y := by
    obtain ⟨γ,hγ⟩ := actual_segment x y
    have hl : LipschitzOnWith (NNReal.mk (dist x y) dist_nonneg) γ.extend (Icc 0 1) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [Path.extend_apply γ ha,Path.extend_apply γ hb,hγ]
      rfl
    have hupper : eVariationOn γ.extend (Icc 0 1) ≤ ENNReal.ofReal (dist x y) := by
      have hb := hl.comp_eVariationOn_le
        (show MapsTo id (Icc (0 : ℝ) 1) (Icc 0 1) from fun _ h => h)
      rw [ENNReal.ofReal_eq_coe_nnreal (dist_nonneg (x := x) (y := y))]
      simpa only [Function.comp_id,eVariationOn_id_Icc,sub_zero,ENNReal.ofReal_one,mul_one] using hb
    have hlower : ENNReal.ofReal (dist x y) ≤ eVariationOn γ.extend (Icc 0 1) := by
      have hb := eVariationOn.edist_le γ.extend (s := Icc 0 1) (x := 0) (y := 1)
        (by norm_num) (by norm_num)
      simpa only [Path.extend_zero,Path.extend_one,edist_dist] using hb
    refine ⟨γ,le_antisymm hupper hlower,?_⟩
    intro t
    have hb : dist x (γ t) = dist x y * (t : ℝ) := by
      simpa [Real.dist_eq,abs_of_nonneg t.property.1] using hγ 0 t
    rw [hb]
    exact mul_le_of_le_one_right dist_nonneg t.property.2
  have actual_cover_locally_isometric_to_H2 (x : P) :
      ∃ (e : OpenPartialHomeomorph P H2) (U : Set P),
        IsOpen U ∧ x ∈ U ∧ U ⊆ e.source ∧
          ∀ y ∈ U, ∀ z ∈ U, dist y z = dist (e y) (e z) := by
    obtain ⟨e,hx,he⟩ := actual_hyperbolic_metric_charts x
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
    let U := e.source ∩ e ⁻¹' Metric.ball (e x) (r / 3)
    have hopen : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
    have hcenter : e x ∈ Metric.ball (e x) (r / 3) := Metric.mem_ball_self (by positivity)
    refine ⟨e,U,hopen,⟨hx,hcenter⟩,fun _ hy => hy.1,?_⟩
    intro y hy z hz
    obtain ⟨δ,hδlength,hδbound⟩ := exact_geodesic_segment (e y) (e z)
    have htarget (t : unitInterval) : δ t ∈ e.target := by
      apply hball
      change dist (δ t) (e x) < r
      have hynear : dist (e y) (e x) < r / 3 := hy.2
      have hznear : dist (e z) (e x) < r / 3 := hz.2
      have htri := dist_triangle (δ t) (e y) (e x)
      have htri' := dist_triangle (e y) (e x) (e z)
      have hbound := hδbound t
      rw [dist_comm (δ t) (e y)] at htri
      rw [dist_comm (e x) (e z)] at htri'
      linarith
    let γ : Path y z := {
      toFun := fun t => e.symm (δ t)
      continuous_toFun := e.continuousOn_symm.comp_continuous δ.continuous htarget
      source' := by rw [δ.source];exact e.left_inv hy.1
      target' := by rw [δ.target];exact e.left_inv hz.1 }
    have hl : LipschitzOnWith 1 (fun w : H2 => (p (e.symm w)).val) e.target := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      change dist (actualProjection (e.symm a)) (actualProjection (e.symm b)) ≤ 1 * dist a b
      rw [he _ (e.map_target ha) _ (e.map_target hb),e.right_inv ha,e.right_inv hb]
      simp
    have hmap : MapsTo δ.extend (Icc 0 1) e.target := by
      intro t ht
      rw [Path.extend_apply δ ht]
      exact htarget ⟨t,ht⟩
    have hlength : eVariationOn (fun t => (p (γ.extend t)).val) (Icc 0 1) ≤
        ENNReal.ofReal (dist (e y) (e z)) := by
      have heq : EqOn (fun t => (p (γ.extend t)).val)
          ((fun w : H2 => (p (e.symm w)).val) ∘ δ.extend) (Icc 0 1) := by
        intro t ht
        change (p (γ.extend t)).val = (p (e.symm (δ.extend t))).val
        rw [Path.extend_apply γ ht,Path.extend_apply δ ht]
        rfl
      rw [eVariationOn.congr heq,←hδlength]
      simpa only [ENNReal.coe_one,one_mul] using hl.comp_eVariationOn_le hmap
    have hupper : D y z ≤ ENNReal.ofReal (dist (e y) (e z)) := by
      rw [hD]
      exact (iInf_le _ γ).trans hlength
    have hlower : ENNReal.ofReal (dist (e y) (e z)) ≤ D y z := by
      have hb := hDbase y z
      change edist (actualProjection y) (actualProjection z) ≤ D y z at hb
      rw [edist_dist,he _ hy.1 _ hz.1] at hb
      exact hb
    have hDeq : D y z = ENNReal.ofReal (dist (e y) (e z)) := le_antisymm hupper hlower
    change (D y z).toReal = dist (e y) (e z)
    rw [hDeq,ENNReal.toReal_ofReal dist_nonneg]
  have actual_metric_chart_locally_isometric (x : P) (e : OpenPartialHomeomorph P H2)
      (hx : x ∈ e.source)
      (he : ∀ y ∈ e.source, ∀ z ∈ e.source,
        dist (actualProjection y) (actualProjection z) = dist (e y) (e z)) :
      ∃ U : Set P, IsOpen U ∧ x ∈ U ∧ U ⊆ e.source ∧
        ∀ y ∈ U, ∀ z ∈ U, dist y z = dist (e y) (e z) := by
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
    let U := e.source ∩ e ⁻¹' Metric.ball (e x) (r / 3)
    have hopen : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
    have hcenter : e x ∈ Metric.ball (e x) (r / 3) := Metric.mem_ball_self (by positivity)
    refine ⟨U,hopen,⟨hx,hcenter⟩,fun _ hy => hy.1,?_⟩
    intro y hy z hz
    obtain ⟨δ,hδlength,hδbound⟩ := exact_geodesic_segment (e y) (e z)
    have htarget (t : unitInterval) : δ t ∈ e.target := by
      apply hball
      change dist (δ t) (e x) < r
      have hynear : dist (e y) (e x) < r / 3 := hy.2
      have hznear : dist (e z) (e x) < r / 3 := hz.2
      have htri := dist_triangle (δ t) (e y) (e x)
      have htri' := dist_triangle (e y) (e x) (e z)
      have hbound := hδbound t
      rw [dist_comm (δ t) (e y)] at htri
      rw [dist_comm (e x) (e z)] at htri'
      linarith
    let γ : Path y z := {
      toFun := fun t => e.symm (δ t)
      continuous_toFun := e.continuousOn_symm.comp_continuous δ.continuous htarget
      source' := by rw [δ.source];exact e.left_inv hy.1
      target' := by rw [δ.target];exact e.left_inv hz.1 }
    have hl : LipschitzOnWith 1 (fun w : H2 => (p (e.symm w)).val) e.target := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      change dist (actualProjection (e.symm a)) (actualProjection (e.symm b)) ≤ 1 * dist a b
      rw [he _ (e.map_target ha) _ (e.map_target hb),e.right_inv ha,e.right_inv hb]
      simp
    have hmap : MapsTo δ.extend (Icc 0 1) e.target := by
      intro t ht
      rw [Path.extend_apply δ ht]
      exact htarget ⟨t,ht⟩
    have hlength : eVariationOn (fun t => (p (γ.extend t)).val) (Icc 0 1) ≤
        ENNReal.ofReal (dist (e y) (e z)) := by
      have heq : EqOn (fun t => (p (γ.extend t)).val)
          ((fun w : H2 => (p (e.symm w)).val) ∘ δ.extend) (Icc 0 1) := by
        intro t ht
        change (p (γ.extend t)).val = (p (e.symm (δ.extend t))).val
        rw [Path.extend_apply γ ht,Path.extend_apply δ ht]
        rfl
      rw [eVariationOn.congr heq,←hδlength]
      simpa only [ENNReal.coe_one,one_mul] using hl.comp_eVariationOn_le hmap
    have hupper : D y z ≤ ENNReal.ofReal (dist (e y) (e z)) := by
      rw [hD]
      exact (iInf_le _ γ).trans hlength
    have hlower : ENNReal.ofReal (dist (e y) (e z)) ≤ D y z := by
      have hb := hDbase y z
      change edist (actualProjection y) (actualProjection z) ≤ D y z at hb
      rw [edist_dist,he _ hy.1 _ hz.1] at hb
      exact hb
    have hDeq : D y z = ENNReal.ofReal (dist (e y) (e z)) := le_antisymm hupper hlower
    change (D y z).toReal = dist (e y) (e z)
    rw [hDeq,ENNReal.toReal_ofReal dist_nonneg]
  have equal_distance_cross (z w a : H2) (h : dist z a = dist w a) :
      ((z.re-a.re)^2+z.im^2+a.im^2)*w.im =
        ((w.re-a.re)^2+w.im^2+a.im^2)*z.im := by
    have hc := congrArg Real.cosh h
    rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist'] at hc
    have hc' := (div_eq_div_iff
      (by positivity : 2*z.im*a.im ≠ 0) (by positivity : 2*w.im*a.im ≠ 0)).mp hc
    apply mul_right_cancel₀ a.im_ne_zero
    nlinarith only [hc']
  have three_anchor_uniqueness (r s : ℝ) (hr : 0 < r) (hs : s ≠ 0) (z w : H2)
      (h0 : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
      (hv : dist z (verticalPath r) = dist w (verticalPath r))
      (ha : dist z (⟨(s : ℂ)+Complex.I,by simp⟩ : H2) =
        dist w (⟨(s : ℂ)+Complex.I,by simp⟩ : H2)) : z = w := by
    have h1 := equal_distance_cross z w UpperHalfPlane.I h0
    have h2 := equal_distance_cross z w (verticalPath r) hv
    have h3 := equal_distance_cross z w (⟨(s : ℂ)+Complex.I,by simp⟩ : H2) ha
    simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,sub_zero,one_pow] at h1
    simp [verticalPath] at h2
    simp only [UpperHalfPlane.mk_re,UpperHalfPlane.mk_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,add_zero,zero_add,one_pow] at h3
    have hprod : ((Real.exp r)^2-1)*(w.im-z.im) = 0 := by nlinarith only [h1,h2]
    have hn : (Real.exp r)^2-1 ≠ 0 := by
      have he := Real.one_lt_exp_iff.mpr hr
      nlinarith [sq_nonneg (Real.exp r-1)]
    have him : z.im = w.im := by
      have hh := (mul_eq_zero.mp hprod).resolve_left hn
      linarith
    rw [←him] at h1 h3
    have hnorm : z.re^2+z.im^2+1 = w.re^2+z.im^2+1 := mul_right_cancel₀ z.im_ne_zero h1
    have hnorm' : (z.re-s)^2+z.im^2+1 = (w.re-s)^2+z.im^2+1 :=
      mul_right_cancel₀ z.im_ne_zero h3
    have hprodre : s*(z.re-w.re) = 0 := by nlinarith only [hnorm,hnorm']
    have hre : z.re = w.re := by
      have hh := (mul_eq_zero.mp hprodre).resolve_left hs
      linarith
    exact UpperHalfPlane.ext_re_im hre him
  have two_anchor_coordinates (r : ℝ) (hr : 0 < r) (z w : H2)
      (h0 : dist z UpperHalfPlane.I = dist w UpperHalfPlane.I)
      (hv : dist z (verticalPath r) = dist w (verticalPath r)) :
      z.im = w.im ∧ z.re^2 = w.re^2 := by
    have h1 := equal_distance_cross z w UpperHalfPlane.I h0
    have h2 := equal_distance_cross z w (verticalPath r) hv
    simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,sub_zero,one_pow] at h1
    simp [verticalPath] at h2
    have hprod : ((Real.exp r)^2-1)*(w.im-z.im) = 0 := by nlinarith only [h1,h2]
    have hn : (Real.exp r)^2-1 ≠ 0 := by
      have he := Real.one_lt_exp_iff.mpr hr
      nlinarith [sq_nonneg (Real.exp r-1)]
    have him : z.im = w.im := by
      have hh := (mul_eq_zero.mp hprod).resolve_left hn
      linarith
    refine ⟨him,?_⟩
    rw [←him] at h1
    have hnorm := mul_right_cancel₀ z.im_ne_zero h1
    linarith
  let verticalReflection : H2 ≃ᵢ H2 := by
    let F : H2 → H2 := fun z => ⟨-star (z : ℂ),by simpa using z.im_pos⟩
    have hinv : Function.Involutive F := by
      intro z
      apply UpperHalfPlane.coe_injective
      simp [F]
    refine { toEquiv := hinv.toPerm F, isometry_toFun := ?_ }
    apply Isometry.of_dist_eq
    intro z w
    change dist (F z) (F w) = dist z w
    simp only [F,UpperHalfPlane.dist_eq,UpperHalfPlane.coe_mk,UpperHalfPlane.mk_im,
      Complex.neg_im,Complex.star_def,Complex.conj_im,neg_neg,dist_neg_neg,Complex.dist_conj_conj,UpperHalfPlane.coe_im]
  have reflection_re (z : H2) : (verticalReflection z).re = -z.re := by
    change (-star (z : ℂ)).re = -z.re
    simp
  have reflection_im (z : H2) : (verticalReflection z).im = z.im := by
    change (-star (z : ℂ)).im = z.im
    simp
  have reflection_I : verticalReflection UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext_re_im <;> simp [reflection_re,reflection_im]
  have reflection_vertical (r : ℝ) : verticalReflection (verticalPath r) = verticalPath r := by
    apply UpperHalfPlane.ext_re_im <;> simp [reflection_re,reflection_im,verticalPath]
  have fixed_three_anchors_identity (r s : ℝ) (hr : 0 < r) (hs : s ≠ 0)
      (U : Set H2) (f : H2 → H2)
      (hmetric : ∀ a ∈ U, ∀ b ∈ U, dist (f a) (f b) = dist a b)
      (hi : UpperHalfPlane.I ∈ U) (hv : verticalPath r ∈ U)
      (hh : (⟨(s : ℂ)+Complex.I,by simp⟩ : H2) ∈ U)
      (hfi : f UpperHalfPlane.I = UpperHalfPlane.I)
      (hfv : f (verticalPath r) = verticalPath r)
      (hfh : f (⟨(s : ℂ)+Complex.I,by simp⟩ : H2) =
        (⟨(s : ℂ)+Complex.I,by simp⟩ : H2)) : ∀ z ∈ U, f z = z := by
    intro z hz
    exact three_anchor_uniqueness r s hr hs (f z) z
      (by simpa only [hfi] using hmetric z hz _ hi)
      (by simpa only [hfv] using hmetric z hz _ hv)
      (by simpa only [hfh] using hmetric z hz _ hh)
  have normalized_overlap_extension (r s : ℝ) (hr : 0 < r) (hs : s ≠ 0)
      (U : Set H2) (f : H2 → H2)
      (hmetric : ∀ a ∈ U, ∀ b ∈ U, dist (f a) (f b) = dist a b)
      (hi : UpperHalfPlane.I ∈ U) (hv : verticalPath r ∈ U)
      (hh : (⟨(s : ℂ)+Complex.I,by simp⟩ : H2) ∈ U)
      (hfi : f UpperHalfPlane.I = UpperHalfPlane.I)
      (hfv : f (verticalPath r) = verticalPath r) :
      ∃ e : H2 ≃ᵢ H2, ∀ z ∈ U, f z = e z := by
    let a : H2 := ⟨(s : ℂ)+Complex.I,by simp⟩
    have h0 : dist (f a) UpperHalfPlane.I = dist a UpperHalfPlane.I := by
      simpa only [hfi] using hmetric a hh _ hi
    have h1 : dist (f a) (verticalPath r) = dist a (verticalPath r) := by
      simpa only [hfv] using hmetric a hh _ hv
    obtain ⟨him,hsq⟩ := two_anchor_coordinates r hr (f a) a h0 h1
    have him' : (f a).im = 1 := by simpa [a] using him
    have hsq' : (f a).re^2 = s^2 := by simpa [a] using hsq
    have hfactor : ((f a).re-s)*((f a).re+s) = 0 := by nlinarith only [hsq']
    rcases mul_eq_zero.mp hfactor with hpos | hneg
    · have hre : (f a).re = s := by linarith
      have hfa : f a = a := UpperHalfPlane.ext_re_im (by simpa [a] using hre) him
      refine ⟨IsometryEquiv.refl H2,?_⟩
      exact fixed_three_anchors_identity r s hr hs U f hmetric hi hv hh hfi hfv hfa
    · have hre : (f a).re = -s := by linarith
      let g := fun z => verticalReflection (f z)
      have hgm : ∀ x ∈ U, ∀ y ∈ U, dist (g x) (g y) = dist x y := by
        intro x hx y hy
        rw [verticalReflection.isometry.dist_eq]
        exact hmetric x hx y hy
      have hgi : g UpperHalfPlane.I = UpperHalfPlane.I := by
        change verticalReflection (f UpperHalfPlane.I) = _
        rw [hfi,reflection_I]
      have hgv : g (verticalPath r) = verticalPath r := by
        change verticalReflection (f (verticalPath r)) = _
        rw [hfv,reflection_vertical]
      have hga : g a = a := by
        apply UpperHalfPlane.ext_re_im
        · change (verticalReflection (f a)).re = a.re
          rw [reflection_re,hre]
          simp [a]
        · exact (reflection_im (f a)).trans him
      have hg := fixed_three_anchors_identity r s hr hs U g hgm hi hv hh hgi hgv hga
      refine ⟨verticalReflection.symm,?_⟩
      intro z hz
      have hgz := congrArg verticalReflection.symm (hg z hz)
      simpa only [g,IsometryEquiv.symm_apply_apply] using hgz
  have anchored_domain_extension (r s : ℝ) (hr : 0 < r) (hs : s ≠ 0)
      (U : Set H2) (f : H2 → H2)
      (hmetric : ∀ a ∈ U, ∀ b ∈ U, dist (f a) (f b) = dist a b)
      (hi : UpperHalfPlane.I ∈ U) (hv : verticalPath r ∈ U)
      (hh : (⟨(s : ℂ)+Complex.I,by simp⟩ : H2) ∈ U) :
      ∃ e : H2 ≃ᵢ H2, ∀ z ∈ U, f z = e z := by
    have hiv : dist UpperHalfPlane.I (verticalPath r) = r := by
      rw [←zero_eq_I,verticalPath_isometry.dist_eq]
      simp [Real.dist_eq,abs_of_nonpos (neg_nonpos.mpr hr.le)]
    obtain ⟨e,he0,he1⟩ := ordered_pair_alignment (f UpperHalfPlane.I) (f (verticalPath r))
    have hpair : dist (f UpperHalfPlane.I) (f (verticalPath r)) = r :=
      (hmetric _ hi _ hv).trans hiv
    rw [hpair] at he1
    let g := fun z => e.symm (f z)
    have hgm : ∀ a ∈ U, ∀ b ∈ U, dist (g a) (g b) = dist a b := by
      intro a ha b hb
      rw [e.symm.isometry.dist_eq]
      exact hmetric a ha b hb
    have hgi : g UpperHalfPlane.I = UpperHalfPlane.I := by
      change e.symm (f UpperHalfPlane.I) = _
      rw [←he0,e.symm_apply_apply]
    have hgv : g (verticalPath r) = verticalPath r := by
      change e.symm (f (verticalPath r)) = _
      rw [←he1,e.symm_apply_apply]
    obtain ⟨T,hT⟩ := normalized_overlap_extension r s hr hs U g hgm hi hv hh hgi hgv
    refine ⟨T.trans e,?_⟩
    intro z hz
    have h := congrArg e (hT z hz)
    simpa only [g,e.apply_symm_apply,IsometryEquiv.trans_apply] using h
  have open_domain_anchors (U : Set H2) (hU : IsOpen U) (hi : UpperHalfPlane.I ∈ U) :
      ∃ r s : ℝ, 0 < r ∧ s ≠ 0 ∧ verticalPath r ∈ U ∧
        (⟨(s : ℂ)+Complex.I,by simp⟩ : H2) ∈ U := by
    let horizontal : ℝ → H2 := fun s => ⟨(s : ℂ)+Complex.I,by simp⟩
    have hhcont : Continuous horizontal :=
      UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
        (Complex.continuous_ofReal.add continuous_const)
    have hh0 : horizontal 0 = UpperHalfPlane.I := by
      apply UpperHalfPlane.coe_injective
      simp [horizontal]
    have hopen : IsOpen (verticalPath ⁻¹' U ∩ horizontal ⁻¹' U) :=
      (hU.preimage verticalPath_isometry.continuous).inter (hU.preimage hhcont)
    have h0 : (0 : ℝ) ∈ verticalPath ⁻¹' U ∩ horizontal ⁻¹' U := by
      simpa only [mem_inter_iff,mem_preimage,zero_eq_I,hh0,and_self] using hi
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
    have hhalf : ε/2 ∈ Metric.ball (0 : ℝ) ε := by
      change dist (ε/2) 0 < ε
      rw [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < ε/2)]
      linarith
    refine ⟨ε/2,ε/2,by positivity,by positivity,?_,?_⟩
    · exact (hball hhalf).1
    · exact (hball hhalf).2
  have hyperbolic_open_domain_global_extension (U : Set H2) (hU : IsOpen U) (f : H2 → H2)
      (hmetric : ∀ a ∈ U, ∀ b ∈ U, dist (f a) (f b) = dist a b) :
      ∃ e : H2 ≃ᵢ H2, ∀ z ∈ U, f z = e z := by
    classical
    by_cases hne : U.Nonempty
    · obtain ⟨x,hx⟩ := hne
      let e0 : H2 ≃ᵢ H2 := IsometryEquiv.constSMul x.toSL2R
      have he0 : e0 UpperHalfPlane.I = x := x.toSL2R_smul_I
      let V := e0 ⁻¹' U
      have hV : IsOpen V := hU.preimage e0.continuous
      have hiV : UpperHalfPlane.I ∈ V := by change e0 UpperHalfPlane.I ∈ U;rwa [he0]
      obtain ⟨r,s,hr,hs,hv,hh⟩ := open_domain_anchors V hV hiV
      let g := fun z => f (e0 z)
      have hgm : ∀ a ∈ V, ∀ b ∈ V, dist (g a) (g b) = dist a b := by
        intro a ha b hb
        rw [hmetric _ ha _ hb,e0.isometry.dist_eq]
      obtain ⟨T,hT⟩ := anchored_domain_extension r s hr hs V g hgm hiV hv hh
      refine ⟨e0.symm.trans T,?_⟩
      intro z hz
      have hzV : e0.symm z ∈ V := by
        change e0 (e0.symm z) ∈ U
        rwa [e0.apply_symm_apply]
      simpa only [g,e0.apply_symm_apply,IsometryEquiv.trans_apply] using hT (e0.symm z) hzV
    · refine ⟨IsometryEquiv.refl H2,?_⟩
      intro z hz
      exact (hne ⟨z,hz⟩).elim
  have actual_hyperbolic_transition_global_extension
      (e f : OpenPartialHomeomorph P H2)
      (he : ∀ y ∈ e.source, ∀ z ∈ e.source,
        dist (actualProjection y) (actualProjection z) = dist (e y) (e z))
      (hf : ∀ y ∈ f.source, ∀ z ∈ f.source,
        dist (actualProjection y) (actualProjection z) = dist (f y) (f z)) :
      ∃ T : H2 ≃ᵢ H2, ∀ z ∈ (e.symm.trans f).source,
        (e.symm.trans f) z = T z := by
    apply hyperbolic_open_domain_global_extension _ (e.symm.trans f).open_source
    intro a ha b hb
    exact (actual_hyperbolic_transition_isometry e f he hf).dist_eq ⟨a,ha⟩ ⟨b,hb⟩
  have hyperbolic_global_isometry_unique_on_open (U : Set H2) (hU : IsOpen U) (hne : U.Nonempty)
      (A B : H2 ≃ᵢ H2) (hAB : ∀ z ∈ U, A z = B z) : A = B := by
    obtain ⟨x,hx⟩ := hne
    let e0 : H2 ≃ᵢ H2 := IsometryEquiv.constSMul x.toSL2R
    have he0 : e0 UpperHalfPlane.I = x := x.toSL2R_smul_I
    let V := e0 ⁻¹' U
    have hV : IsOpen V := hU.preimage e0.continuous
    have hiV : UpperHalfPlane.I ∈ V := by change e0 UpperHalfPlane.I ∈ U;rwa [he0]
    obtain ⟨r,s,hr,hs,hv,hh⟩ := open_domain_anchors V hV hiV
    let A0 := e0.trans A
    let B0 := e0.trans B
    let F := A0.trans B0.symm
    have hfix (z : H2) (hz : z ∈ V) : F z = z := by
      change e0.symm (B.symm (A (e0 z))) = z
      rw [hAB _ hz,B.symm_apply_apply,e0.symm_apply_apply]
    have hid : ∀ z ∈ (Set.univ : Set H2), F z = z :=
      fixed_three_anchors_identity r s hr hs univ F
        (fun a _ b _ => F.isometry.dist_eq a b) (mem_univ _) (mem_univ _) (mem_univ _)
        (hfix _ hiV) (hfix _ hv) (hfix _ hh)
    apply IsometryEquiv.ext
    intro z
    have h : A0 (e0.symm z) = B0 (e0.symm z) := by
      calc A0 (e0.symm z) = B0 (F (e0.symm z)) := by
             change A0 (e0.symm z) = B0 (B0.symm (A0 (e0.symm z)))
             rw [B0.apply_symm_apply]
           _ = B0 (e0.symm z) := congrArg B0 (hid _ (mem_univ _))
    simpa only [A0,B0,IsometryEquiv.trans_apply,e0.apply_symm_apply] using h
  have actual_hyperbolic_transition_global_extension_unique
      (e f : OpenPartialHomeomorph P H2)
      (he : ∀ y ∈ e.source, ∀ z ∈ e.source,
        dist (actualProjection y) (actualProjection z) = dist (e y) (e z))
      (hf : ∀ y ∈ f.source, ∀ z ∈ f.source,
        dist (actualProjection y) (actualProjection z) = dist (f y) (f z))
      (hne : (e.symm.trans f).source.Nonempty) :
      ∃! T : H2 ≃ᵢ H2, ∀ z ∈ (e.symm.trans f).source,
        (e.symm.trans f) z = T z := by
    obtain ⟨T,hT⟩ := actual_hyperbolic_transition_global_extension e f he hf
    refine ⟨T,hT,?_⟩
    intro R hR
    apply hyperbolic_global_isometry_unique_on_open _ (e.symm.trans f).open_source hne
    intro z hz
    exact (hR z hz).symm.trans (hT z hz)
  have actual_global_transition_cocycle
      (e f g : OpenPartialHomeomorph P H2) (Tef Tfg Teg : H2 ≃ᵢ H2)
      (hEF : ∀ z ∈ (e.symm.trans f).source, (e.symm.trans f) z = Tef z)
      (hFG : ∀ z ∈ (f.symm.trans g).source, (f.symm.trans g) z = Tfg z)
      (hEG : ∀ z ∈ (e.symm.trans g).source, (e.symm.trans g) z = Teg z)
      (x : P) (hxE : x ∈ e.source) (hxF : x ∈ f.source) (hxG : x ∈ g.source) :
      Tef.trans Tfg = Teg := by
    let U := e.source ∩ (f.source ∩ g.source)
    have hopen : IsOpen U := e.open_source.inter (f.open_source.inter g.open_source)
    have hUe : U ⊆ e.source := fun _ h => h.1
    apply hyperbolic_global_isometry_unique_on_open (e '' U)
      (e.isOpen_image_of_subset_source hopen hUe) ⟨e x,⟨x,⟨hxE,hxF,hxG⟩,rfl⟩⟩
    rintro z ⟨y,hy,rfl⟩
    have hsourceEF : e y ∈ (e.symm.trans f).source := by
      refine ⟨e.map_source hy.1,?_⟩
      change e.symm (e y) ∈ f.source
      rw [e.left_inv hy.1]
      exact hy.2.1
    have hsourceFG : f y ∈ (f.symm.trans g).source := by
      refine ⟨f.map_source hy.2.1,?_⟩
      change f.symm (f y) ∈ g.source
      rw [f.left_inv hy.2.1]
      exact hy.2.2
    have hsourceEG : e y ∈ (e.symm.trans g).source := by
      refine ⟨e.map_source hy.1,?_⟩
      change e.symm (e y) ∈ g.source
      rw [e.left_inv hy.1]
      exact hy.2.2
    have heqEF : Tef (e y) = f y := by
      rw [←hEF _ hsourceEF]
      change f (e.symm (e y)) = f y
      rw [e.left_inv hy.1]
    have heqFG : Tfg (f y) = g y := by
      rw [←hFG _ hsourceFG]
      change g (f.symm (f y)) = g y
      rw [f.left_inv hy.2.1]
    have heqEG : Teg (e y) = g y := by
      rw [←hEG _ hsourceEG]
      change g (e.symm (e y)) = g y
      rw [e.left_inv hy.1]
    rw [IsometryEquiv.trans_apply,heqEF,heqFG,heqEG]
  let chart : P → OpenPartialHomeomorph P H2 :=
    fun i => Classical.choose (actual_hyperbolic_metric_charts i)
  have chart_spec (i : P) : i ∈ (chart i).source ∧
      ∀ y ∈ (chart i).source, ∀ z ∈ (chart i).source,
        dist (actualProjection y) (actualProjection z) = dist (chart i y) (chart i z) :=
    Classical.choose_spec (actual_hyperbolic_metric_charts i)
  let transition : P → P → H2 ≃ᵢ H2 := fun i j => Classical.choose
    (actual_hyperbolic_transition_global_extension (chart i) (chart j)
      (chart_spec i).2 (chart_spec j).2)
  have transition_spec (i j : P) (z : H2)
      (hz : z ∈ ((chart i).symm.trans (chart j)).source) :
      ((chart i).symm.trans (chart j)) z = transition i j z :=
    Classical.choose_spec (actual_hyperbolic_transition_global_extension (chart i) (chart j)
      (chart_spec i).2 (chart_spec j).2) z hz
  have transition_at (i j x : P) (hi : x ∈ (chart i).source)
      (hj : x ∈ (chart j).source) : transition i j (chart i x) = chart j x := by
    have hsrc : chart i x ∈ ((chart i).symm.trans (chart j)).source := by
      refine ⟨(chart i).map_source hi,?_⟩
      change (chart i).symm (chart i x) ∈ (chart j).source
      rw [(chart i).left_inv hi]
      exact hj
    rw [←transition_spec i j _ hsrc]
    change chart j ((chart i).symm (chart i x)) = chart j x
    rw [(chart i).left_inv hi]
  have transition_self (i : P) : transition i i = IsometryEquiv.refl H2 := by
    apply hyperbolic_global_isometry_unique_on_open (chart i).target
      (chart i).open_target ⟨chart i i,(chart i).map_source (chart_spec i).1⟩
    intro z hz
    have hx := (chart i).map_target hz
    have h := transition_at i i ((chart i).symm z) hx hx
    change transition i i z = z
    simpa only [(chart i).right_inv hz] using h
  have transition_cocycle (i j k x : P) (hi : x ∈ (chart i).source)
      (hj : x ∈ (chart j).source) (hk : x ∈ (chart k).source) :
      (transition i j).trans (transition j k) = transition i k :=
    actual_global_transition_cocycle (chart i) (chart j) (chart k)
      (transition i j) (transition j k) (transition i k)
      (transition_spec i j) (transition_spec j k) (transition_spec i k) x hi hj hk
  let GermRep := Σ i : P, {x : P // x ∈ (chart i).source} × (H2 ≃ᵢ H2)
  let germPoint : GermRep → P := fun a => a.2.1.val
  let germRel : GermRep → GermRep → Prop := fun a b =>
    germPoint a = germPoint b ∧ a.2.2 = (transition a.1 b.1).trans b.2.2
  have germRel_refl (a : GermRep) : germRel a a := by
    refine ⟨rfl,?_⟩
    change a.2.2 = (transition a.1 a.1).trans a.2.2
    rw [transition_self]
    apply IsometryEquiv.ext
    intro z
    rfl
  have germRel_symm {a b : GermRep} (h : germRel a b) : germRel b a := by
    refine ⟨h.1.symm,?_⟩
    have ha : germPoint a ∈ (chart a.1).source := a.2.1.property
    have hb : germPoint a ∈ (chart b.1).source := h.1.symm ▸ b.2.1.property
    have hinv := transition_cocycle b.1 a.1 b.1 (germPoint a) hb ha hb
    rw [transition_self] at hinv
    change b.2.2 = (transition b.1 a.1).trans a.2.2
    rw [h.2]
    apply IsometryEquiv.ext
    intro z
    have hc := congrArg (fun T : H2 ≃ᵢ H2 => T z) hinv
    change b.2.2 z = b.2.2 (transition a.1 b.1 (transition b.1 a.1 z))
    change transition a.1 b.1 (transition b.1 a.1 z) = z at hc
    rw [hc]
  have germRel_trans {a b c : GermRep} (hab : germRel a b) (hbc : germRel b c) :
      germRel a c := by
    refine ⟨hab.1.trans hbc.1,?_⟩
    have ha : germPoint a ∈ (chart a.1).source := a.2.1.property
    have hb : germPoint a ∈ (chart b.1).source := hab.1.symm ▸ b.2.1.property
    have hc : germPoint a ∈ (chart c.1).source :=
      (hab.1.trans hbc.1).symm ▸ c.2.1.property
    have hcomp := transition_cocycle a.1 b.1 c.1 (germPoint a) ha hb hc
    change a.2.2 = (transition a.1 c.1).trans c.2.2
    rw [hab.2,hbc.2]
    apply IsometryEquiv.ext
    intro z
    exact congrArg c.2.2 (congrArg (fun T : H2 ≃ᵢ H2 => T z) hcomp)
  let germSetoid : Setoid GermRep := ⟨germRel,⟨germRel_refl,germRel_symm,germRel_trans⟩⟩
  let Germ := Quotient germSetoid
  let germProjection : Germ → P := Quotient.lift germPoint (fun _ _ h => h.1)
  have germProjection_surjective : Function.Surjective germProjection := by
    intro x
    exact ⟨Quotient.mk germSetoid ⟨x,⟨⟨x,(chart_spec x).1⟩,IsometryEquiv.refl H2⟩⟩,rfl⟩
  let germEvalRep : GermRep → H2 := fun a => a.2.2 (chart a.1 (germPoint a))
  have germEval_respects {a b : GermRep} (h : germRel a b) :
      germEvalRep a = germEvalRep b := by
    have ha : germPoint a ∈ (chart a.1).source := a.2.1.property
    have hb : germPoint a ∈ (chart b.1).source := h.1.symm ▸ b.2.1.property
    change a.2.2 (chart a.1 (germPoint a)) = b.2.2 (chart b.1 (germPoint b))
    rw [h.2,IsometryEquiv.trans_apply,transition_at a.1 b.1 _ ha hb,h.1]
  let germEvaluation : Germ → H2 := Quotient.lift germEvalRep
    (fun _ _ h => germEval_respects h)
  let germChart (i : P) (x : {x : P // x ∈ (chart i).source}) (T : H2 ≃ᵢ H2) : Germ :=
    Quotient.mk germSetoid ⟨i,⟨x,T⟩⟩
  have germChart_injective (i : P) (x : {x : P // x ∈ (chart i).source})
      (T R : H2 ≃ᵢ H2) : germChart i x T = germChart i x R ↔ T = R := by
    constructor
    · intro h
      have hr := Quotient.exact h
      change x.val = x.val ∧ T = (transition i i).trans R at hr
      have heq := hr.2
      rw [transition_self] at heq
      apply IsometryEquiv.ext
      intro z
      exact congrArg (fun F : H2 ≃ᵢ H2 => F z) heq
    · intro h
      rw [h]
  have germChart_surjective (i : P) (g : Germ)
      (hg : germProjection g ∈ (chart i).source) :
      ∃! T : H2 ≃ᵢ H2, germChart i ⟨germProjection g,hg⟩ T = g := by
    induction g using Quotient.inductionOn with
    | h a =>
      have ha : germPoint a ∈ (chart a.1).source := a.2.1.property
      change germPoint a ∈ (chart i).source at hg
      let T := (transition i a.1).trans a.2.2
      refine ⟨T,?_,?_⟩
      · apply Quotient.sound
        change germPoint a = germPoint a ∧ T = (transition i a.1).trans a.2.2
        exact ⟨rfl,rfl⟩
      · intro R hR
        apply (germChart_injective i ⟨germPoint a,hg⟩ R T).mp
        exact hR.trans (Quotient.sound (show germRel ⟨i,⟨⟨germPoint a,hg⟩,T⟩⟩ a from
          ⟨rfl,rfl⟩)).symm
  let germCoordinates (i : P) : {g : Germ // germProjection g ∈ (chart i).source} ≃
      {x : P // x ∈ (chart i).source} × (H2 ≃ᵢ H2) := {
    toFun := fun g => (⟨germProjection g.val,g.property⟩,
      Classical.choose (germChart_surjective i g.val g.property))
    invFun := fun z => ⟨germChart i z.1 z.2,z.1.property⟩
    left_inv := by
      intro g
      apply Subtype.ext
      exact (Classical.choose_spec (germChart_surjective i g.val g.property)).1
    right_inv := by
      rintro ⟨x,T⟩
      apply Prod.ext
      · rfl
      · apply (germChart_injective i x _ T).mp
        exact (Classical.choose_spec
          (germChart_surjective i (germChart i x T) x.property)).1 }
  let germTopology : TopologicalSpace Germ := {
    IsOpen := fun U => ∀ (i : P) (T : H2 ≃ᵢ H2),
      IsOpen ((fun x : {x : P // x ∈ (chart i).source} => germChart i x T) ⁻¹' U)
    isOpen_univ := by
      intro i T
      simp only [Set.preimage_univ]
      exact isOpen_univ
    isOpen_inter := by
      intro U V hU hV i T
      rw [Set.preimage_inter]
      exact (hU i T).inter (hV i T)
    isOpen_sUnion := by
      intro S hS i T
      rw [Set.preimage_sUnion]
      apply isOpen_biUnion
      intro U hU
      exact hS U hU i T }
  letI : TopologicalSpace Germ := germTopology
  have germChart_continuous (i : P) (T : H2 ≃ᵢ H2) :
      Continuous (fun x : {x : P // x ∈ (chart i).source} => germChart i x T) := by
    apply continuous_def.mpr
    intro U hU
    exact hU i T
  have germProjection_continuous : Continuous germProjection := by
    apply continuous_def.mpr
    intro U hU i T
    change IsOpen ((fun x : {x : P // x ∈ (chart i).source} => x.val) ⁻¹' U)
    exact hU.preimage continuous_subtype_val
  have germEvaluation_continuous : Continuous germEvaluation := by
    apply continuous_def.mpr
    intro U hU i T
    change IsOpen ((fun x : {x : P // x ∈ (chart i).source} => T (chart i x.val)) ⁻¹' U)
    apply hU.preimage
    exact T.continuous.comp ((chart i).continuousOn.restrict)
  let germSheet (i : P) (T : H2 ≃ᵢ H2) (V : Set P) : Set Germ :=
    (fun x : {x : P // x ∈ (chart i).source} => germChart i x T) ''
      {x | x.val ∈ V}
  have germSheet_membership (i j : P) (T R : H2 ≃ᵢ H2) (V : Set P)
      (hV : V ⊆ (chart i).source) (x : {x : P // x ∈ (chart j).source}) :
      germChart j x R ∈ germSheet i T V ↔
        x.val ∈ V ∧ R = (transition j i).trans T := by
    constructor
    · rintro ⟨y,hy,heq⟩
      have hr := Quotient.exact heq.symm
      change x.val = y.val ∧ R = (transition j i).trans T at hr
      exact ⟨hr.1 ▸ hy,hr.2⟩
    · rintro ⟨hx,hR⟩
      refine ⟨⟨x.val,hV hx⟩,hx,?_⟩
      apply Quotient.sound
      apply germRel_symm
      exact ⟨rfl,hR⟩
  have germSheet_open (i : P) (T : H2 ≃ᵢ H2) (V : Set P)
      (hV : IsOpen V) (hVi : V ⊆ (chart i).source) : IsOpen (germSheet i T V) := by
    intro j R
    by_cases hR : R = (transition j i).trans T
    · have heq : (fun x : {x : P // x ∈ (chart j).source} => germChart j x R) ⁻¹'
          germSheet i T V = Subtype.val ⁻¹' V := by
        ext x
        exact (germSheet_membership i j T R V hVi x).trans (and_iff_left hR)
      rw [heq]
      exact hV.preimage continuous_subtype_val
    · have heq : (fun x : {x : P // x ∈ (chart j).source} => germChart j x R) ⁻¹'
          germSheet i T V = ∅ := by
        ext x
        simp only [Set.mem_preimage,Set.mem_empty_iff_false]
        rw [germSheet_membership i j T R V hVi x]
        simp only [hR,and_false]
      rw [heq]
      exact isOpen_empty
  have germChart_openEmbedding (i : P) (T : H2 ≃ᵢ H2) :
      IsOpenEmbedding (fun x : {x : P // x ∈ (chart i).source} => germChart i x T) := by
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap (germChart_continuous i T)
    · intro x y h
      apply Subtype.ext
      exact congrArg germProjection h
    · intro U hU
      let V : Set P := Subtype.val '' U
      have hV : IsOpen V := (chart i).open_source.isOpenMap_subtype_val U hU
      have hVi : V ⊆ (chart i).source := by
        rintro _ ⟨x,hx,rfl⟩
        exact x.property
      have hpre : {x : {x : P // x ∈ (chart i).source} | x.val ∈ V} = U := by
        ext x
        constructor
        · rintro ⟨y,hy,heq⟩
          have hxy : y = x := Subtype.ext heq
          rwa [←hxy]
        · intro hx
          exact ⟨x,hx,rfl⟩
      have hopen := germSheet_open i T V hV hVi
      change IsOpen ((fun x : {x : P // x ∈ (chart i).source} => germChart i x T) ''
        {x | x.val ∈ V}) at hopen
      rwa [hpre] at hopen
  letI : TopologicalSpace (H2 ≃ᵢ H2) := ⊥
  letI : DiscreteTopology (H2 ≃ᵢ H2) := ⟨rfl⟩
  have germCoordinates_inverse_continuous (i : P) : Continuous (germCoordinates i).symm := by
    apply continuous_prod_of_discrete_right.mpr
    intro T
    exact (germChart_continuous i T).subtype_mk _
  have germCoordinates_inverse_open (i : P) : IsOpenMap (germCoordinates i).symm := by
    apply isOpenMap_prod_of_discrete_right.mpr
    intro T
    exact (germChart_openEmbedding i T).isOpenMap.subtype_mk _
  let germCoordinatesHomeomorph (i : P) :
      {g : Germ // germProjection g ∈ (chart i).source} ≃ₜ
        {x : P // x ∈ (chart i).source} × (H2 ≃ᵢ H2) :=
    ((germCoordinates i).symm.toHomeomorphOfContinuousOpen
      (germCoordinates_inverse_continuous i) (germCoordinates_inverse_open i)).symm
  have germProjection_evenlyCovered (i : P) :
      IsEvenlyCovered germProjection i (H2 ≃ᵢ H2) := by
    refine ⟨inferInstance,(chart i).source,(chart_spec i).1,(chart i).open_source,
      (chart i).open_source.preimage germProjection_continuous,
      germCoordinatesHomeomorph i,?_⟩
    intro g
    rfl
  have germProjection_covering : IsCoveringMap germProjection := by
    intro i
    exact (germProjection_evenlyCovered i).to_isEvenlyCovered_preimage
  letI : ChartedSpace H2 P := {
    atlas := Set.range chart
    chartAt := chart
    mem_chart_source := fun x => (chart_spec x).1
    chart_mem_atlas := fun x => Set.mem_range_self x }
  letI : LocallyPathConnectedSpace P := ChartedSpace.locallyPathConnectedSpace H2 P
  let a : P := Classical.choice (inferInstance : Nonempty P)
  let initialGerm : Germ := germChart a ⟨a,(chart_spec a).1⟩ (IsometryEquiv.refl H2)
  obtain ⟨developingSection,hsection,hunique⟩ :=
    germProjection_covering.existsUnique_continuousMap_lifts (ContinuousMap.id P) a initialGerm rfl
  have developingSection_projects (x : P) : germProjection (developingSection x) = x :=
    congrFun hsection.2 x
  let actualDevelopment : C(P,H2) :=
    (⟨germEvaluation,germEvaluation_continuous⟩ : C(Germ,H2)).comp developingSection
  have actualDevelopment_local_formula (x : P) :
      ∃ (U : Set P) (T : H2 ≃ᵢ H2), IsOpen U ∧ x ∈ U ∧
        U ⊆ (chart x).source ∧ ∀ y ∈ U, actualDevelopment y = T (chart x y) := by
    have hx : germProjection (developingSection x) ∈ (chart x).source := by
      rw [developingSection_projects]
      exact (chart_spec x).1
    obtain ⟨T,hT,huniq⟩ := germChart_surjective x (developingSection x) hx
    let U := developingSection ⁻¹' germSheet x T (chart x).source
    have hU : IsOpen U := (germSheet_open x T (chart x).source (chart x).open_source
      Set.Subset.rfl).preimage developingSection.continuous
    have hxU : x ∈ U := by
      exact ⟨⟨germProjection (developingSection x),hx⟩,hx,hT⟩
    have hform (y : P) (hy : y ∈ U) :
        y ∈ (chart x).source ∧ actualDevelopment y = T (chart x y) := by
      obtain ⟨z,hz,hzg⟩ := hy
      have hpoint : z.val = y := by
        have h := congrArg germProjection hzg
        exact h.trans (developingSection_projects y)
      refine ⟨hpoint ▸ z.property,?_⟩
      have heval := congrArg germEvaluation hzg
      change T (chart x z.val) = actualDevelopment y at heval
      rw [hpoint] at heval
      exact heval.symm
    exact ⟨U,T,hU,hxU,fun y hy => (hform y hy).1,fun y hy => (hform y hy).2⟩
  have actualDevelopment_locally_isometric (x : P) :
      ∃ U : Set P, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U, dist (actualDevelopment y) (actualDevelopment z) = dist y z := by
    obtain ⟨V,T,hV,hxV,hVi,hform⟩ := actualDevelopment_local_formula x
    obtain ⟨U,hU,hxU,hUi,hmetric⟩ := actual_metric_chart_locally_isometric x (chart x)
      (chart_spec x).1 (chart_spec x).2
    refine ⟨V ∩ U,hV.inter hU,⟨hxV,hxU⟩,?_⟩
    intro y hy z hz
    rw [hform y hy.1,hform z hz.1,T.isometry.dist_eq]
    exact (hmetric y hy.2 z hz.2).symm
  have actualDevelopment_localHomeomorph : IsLocalHomeomorph actualDevelopment := by
    apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
    intro x
    obtain ⟨U,T,hU,hxU,hUi,hform⟩ := actualDevelopment_local_formula x
    refine ⟨U,hU.mem_nhds hxU,?_⟩
    have hinc : IsOpenEmbedding (Set.inclusion hUi) :=
      Topology.IsOpenEmbedding.inclusion hUi (hU.preimage continuous_subtype_val)
    have he := T.toHomeomorph.isOpenEmbedding.comp
      ((chart x).isOpenEmbedding_restrict.comp hinc)
    convert he using 1
    funext y
    exact hform y.val y.property
  let Interval : Type := ↥(Set.Icc (0 : ℝ) 1)
  have lifted_path_endpoint_bound (K : NNReal) (Γ : C(Interval,P))
      (δ : C(Interval,H2)) (hδ : LipschitzWith K δ)
      (hlift : ∀ t, actualDevelopment (Γ t) = δ t) :
      dist (Γ 0) (Γ 1) ≤ (K : ℝ) := by
    choose U hU hxU hmetric using actualDevelopment_locally_isometric
    let V : Interval → Set Interval := fun t => Γ ⁻¹' U (Γ t)
    have hV (t : Interval) : IsOpen (V t) := (hU (Γ t)).preimage Γ.continuous
    have hcover : Set.univ ⊆ ⋃ t, V t := by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨t,hxU (Γ t)⟩
    obtain ⟨t,ht0,htmono,⟨N,hN⟩,hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval hV hcover
    have hstep (n : ℕ) : dist (Γ (t n)) (Γ (t (n+1))) ≤
        (K : ℝ) * ((t (n+1) : ℝ) - (t n : ℝ)) := by
      obtain ⟨j,hj⟩ := hsub n
      have hle : t n ≤ t (n+1) := htmono (Nat.le_succ n)
      have hleft := hj (show t n ∈ Set.Icc (t n) (t (n+1)) from ⟨le_rfl,hle⟩)
      have hright := hj (show t (n+1) ∈ Set.Icc (t n) (t (n+1)) from ⟨hle,le_rfl⟩)
      have heq := hmetric (Γ j) (Γ (t n)) hleft (Γ (t (n+1))) hright
      rw [hlift,hlift] at heq
      rw [←heq]
      have h := hδ.dist_le_mul (t n) (t (n+1))
      have hleR : (t n : ℝ) ≤ (t (n+1) : ℝ) := hle
      rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hleR)] at h
      simpa only [neg_sub] using h
    have hbound (n : ℕ) : dist (Γ (t 0)) (Γ (t n)) ≤
        (K : ℝ) * ((t n : ℝ) - (t 0 : ℝ)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have htri := dist_triangle (Γ (t 0)) (Γ (t n)) (Γ (t (n+1)))
        have hsn := hstep n
        nlinarith
    have h := hbound N
    rw [ht0,hN N le_rfl] at h
    simpa using h
  have lifted_path_lipschitz (K : NNReal) (Γ : C(Interval,P))
      (δ : C(Interval,H2)) (hδ : LipschitzWith K δ)
      (hlift : ∀ t, actualDevelopment (Γ t) = δ t) : LipschitzWith K Γ := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    let ρ : C(Interval,Interval) := {
      toFun := fun u => Set.projIcc 0 1 zero_le_one
        (AffineMap.lineMap (s : ℝ) (t : ℝ) (u : ℝ))
      continuous_toFun := (LipschitzWith.projIcc zero_le_one).continuous.comp
        ((lipschitzWith_lineMap (s : ℝ) (t : ℝ)).continuous.comp continuous_subtype_val) }
    have hρ : LipschitzWith (nndist s t) ρ := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      have hproj := (LipschitzWith.projIcc zero_le_one).dist_le_mul
        (AffineMap.lineMap (s : ℝ) (t : ℝ) (u : ℝ))
        (AffineMap.lineMap (s : ℝ) (t : ℝ) (v : ℝ))
      have hline := (lipschitzWith_lineMap (s : ℝ) (t : ℝ)).dist_le_mul (u : ℝ) (v : ℝ)
      have hp : dist (ρ u) (ρ v) ≤ dist (AffineMap.lineMap (s : ℝ) (t : ℝ) (u : ℝ))
          (AffineMap.lineMap (s : ℝ) (t : ℝ) (v : ℝ)) := by
        simpa only [ρ,ContinuousMap.coe_mk,NNReal.coe_one,one_mul] using hproj
      exact hp.trans hline
    have h0 : ρ 0 = s := by
      change Set.projIcc 0 1 zero_le_one (AffineMap.lineMap (s : ℝ) (t : ℝ) 0) = s
      rw [AffineMap.lineMap_apply_zero,Set.projIcc_of_mem zero_le_one s.property]
    have h1 : ρ 1 = t := by
      change Set.projIcc 0 1 zero_le_one (AffineMap.lineMap (s : ℝ) (t : ℝ) 1) = t
      rw [AffineMap.lineMap_apply_one,Set.projIcc_of_mem zero_le_one t.property]
    have h := lifted_path_endpoint_bound (K * nndist s t) (Γ.comp ρ) (δ.comp ρ)
      (hδ.comp hρ) (fun u => hlift (ρ u))
    simpa only [ContinuousMap.comp_apply,h0,h1,NNReal.coe_mul,coe_nndist] using h
  have partial_lift_lipschitz (R : ℝ) (K : NNReal)
      (γ : C(↥(Set.Ico (0 : ℝ) R),P)) (δ : C(ℝ,H2))
      (hδ : LipschitzWith K δ) (hlift : ∀ t, actualDevelopment (γ t) = δ t.val) :
      LipschitzWith K γ := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    let ρ : C(Interval,↥(Set.Ico (0 : ℝ) R)) := {
      toFun := fun u => ⟨AffineMap.lineMap (s : ℝ) (t : ℝ) (u : ℝ),
        (convex_Ico (0 : ℝ) R).lineMap_mem s.property t.property u.property⟩
      continuous_toFun := ((lipschitzWith_lineMap (s : ℝ) (t : ℝ)).continuous.comp
        continuous_subtype_val).subtype_mk _ }
    let ρreal : C(Interval,ℝ) := ⟨fun u => (ρ u).val,continuous_subtype_val.comp ρ.continuous⟩
    have hρ : LipschitzWith (nndist s t) ρreal := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      exact (lipschitzWith_lineMap (s : ℝ) (t : ℝ)).dist_le_mul (u : ℝ) (v : ℝ)
    have h0 : ρ 0 = s := by
      apply Subtype.ext
      exact AffineMap.lineMap_apply_zero _ _
    have h1 : ρ 1 = t := by
      apply Subtype.ext
      exact AffineMap.lineMap_apply_one _ _
    have h := lifted_path_endpoint_bound (K * nndist s t) (γ.comp ρ) (δ.comp ρreal)
      (hδ.comp hρ) (fun u => hlift (ρ u))
    simpa only [ContinuousMap.comp_apply,h0,h1,NNReal.coe_mul,coe_nndist] using h
  letI : CompleteSpace P := actual_cover_complete
  have partial_lift_endpoint_completion (R : ℝ) (hR : 0 < R) (K : NNReal)
      (γ : C(↥(Set.Ico (0 : ℝ) R),P)) (δ : C(ℝ,H2))
      (hδ : LipschitzWith K δ) (hlift : ∀ t, actualDevelopment (γ t) = δ t.val) :
      ∃ Γ : C(↥(Set.Icc (0 : ℝ) R),P),
        (∀ t : ↥(Set.Ico (0 : ℝ) R), Γ ⟨t.val,⟨t.property.1,t.property.2.le⟩⟩ = γ t) ∧
        ∀ t, actualDevelopment (Γ t) = δ t.val := by
    let incl : ↥(Set.Ico (0 : ℝ) R) → ↥(Set.Icc (0 : ℝ) R) :=
      Set.inclusion Set.Ico_subset_Icc_self
    have hi : Isometry incl := by
      intro x y
      rfl
    have hd : DenseRange incl := by
      apply (denseRange_inclusion_iff Set.Ico_subset_Icc_self).mpr
      rw [closure_Ico hR.ne]
    let denseIncl := hi.isUniformInducing.isDenseInducing hd
    let F := denseIncl.extend γ
    have hF : UniformContinuous F := uniformContinuous_uniformly_extend hi.isUniformInducing hd
      (partial_lift_lipschitz R K γ δ hδ hlift).uniformContinuous
    have hFγ (t : ↥(Set.Ico (0 : ℝ) R)) : F (incl t) = γ t :=
      denseIncl.extend_eq_at γ.continuous.continuousAt
    have hproj : actualDevelopment ∘ F = fun t : ↥(Set.Icc (0 : ℝ) R) => δ t.val := by
      apply hd.equalizer (actualDevelopment.continuous.comp hF.continuous)
        (δ.continuous.comp continuous_subtype_val)
      funext t
      change actualDevelopment (F (incl t)) = δ t.val
      rw [hFγ]
      exact hlift t
    exact ⟨⟨F,hF.continuous⟩,hFγ,fun t => congrFun hproj t⟩
  have local_path_continuation (R : ℝ) (x : P) (δ : C(ℝ,H2))
      (hx : actualDevelopment x = δ R) :
      ∃ ε : ℝ, 0 < ε ∧ ∃ κ : C(↥(Set.Icc (R-ε) (R+ε)),P),
        (∀ h : R ∈ Set.Icc (R-ε) (R+ε), κ ⟨R,h⟩ = x) ∧
        ∀ t, actualDevelopment (κ t) = δ t.val := by
    obtain ⟨e,hxe,he⟩ := actualDevelopment_localHomeomorph x
    have hRtarget : δ R ∈ e.target := by
      rw [←hx,he]
      exact e.map_source hxe
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp
      (e.open_target.preimage δ.continuous) R hRtarget
    let ε := r / 2
    have hε : 0 < ε := by dsimp [ε];positivity
    have htarget (t : ↥(Set.Icc (R-ε) (R+ε))) : δ t.val ∈ e.target := by
      apply hball
      change |t.val - R| < r
      have ht0 := t.property.1
      have ht1 := t.property.2
      rw [abs_lt]
      dsimp [ε] at ht0 ht1
      constructor <;> linarith
    let κ : C(↥(Set.Icc (R-ε) (R+ε)),P) := {
      toFun := fun t => e.symm (δ t.val)
      continuous_toFun := e.continuousOn_symm.comp_continuous
        (δ.continuous.comp continuous_subtype_val) htarget }
    refine ⟨ε,hε,κ,?_,?_⟩
    · intro h
      change e.symm (δ R) = x
      rw [←hx,he]
      exact e.left_inv hxe
    · intro t
      change actualDevelopment (e.symm (δ t.val)) = δ t.val
      rw [he]
      exact e.right_inv (htarget t)
  have closed_lift_continues (R : ℝ) (hR : 0 ≤ R)
      (Γ : C(↥(Set.Icc (0 : ℝ) R),P)) (δ : C(ℝ,H2))
      (hlift : ∀ t, actualDevelopment (Γ t) = δ t.val) :
      ∃ S : ℝ, R < S ∧ ∃ F : C(↥(Set.Icc (0 : ℝ) S),P),
        (∀ (t : ↥(Set.Icc (0 : ℝ) R)) (h : t.val ∈ Set.Icc 0 S), F ⟨t.val,h⟩ = Γ t) ∧
        ∀ t, actualDevelopment (F t) = δ t.val := by
    let rpoint : ↥(Set.Icc (0 : ℝ) R) := ⟨R,⟨hR,le_rfl⟩⟩
    obtain ⟨ε,hε,κ,hκR,hκlift⟩ := local_path_continuation R (Γ rpoint) δ (hlift rpoint)
    have hεbounds : R-ε ≤ R+ε := by linarith
    let left : C(ℝ,P) := {
      toFun := fun t => Γ (Set.projIcc 0 R hR t)
      continuous_toFun := Γ.continuous.comp (LipschitzWith.projIcc hR).continuous }
    let right : C(ℝ,P) := {
      toFun := fun t => κ (Set.projIcc (R-ε) (R+ε) hεbounds t)
      continuous_toFun := κ.continuous.comp (LipschitzWith.projIcc hεbounds).continuous }
    have hmatch : left R = right R := by
      change Γ (Set.projIcc 0 R hR R) = κ (Set.projIcc (R-ε) (R+ε) hεbounds R)
      rw [Set.projIcc_of_mem hR (show R ∈ Set.Icc 0 R from ⟨hR,le_rfl⟩),
        Set.projIcc_of_mem hεbounds (show R ∈ Set.Icc (R-ε) (R+ε) from ⟨by linarith,by linarith⟩)]
      exact (hκR _).symm
    let pasted : C(ℝ,P) := {
      toFun := fun t => if t ≤ R then left t else right t
      continuous_toFun := left.continuous.if_le right.continuous continuous_id continuous_const
        (fun t ht => by change t = R at ht;simpa only [ht] using hmatch) }
    let F : C(↥(Set.Icc (0 : ℝ) (R+ε)),P) :=
      ⟨fun t => pasted t.val,pasted.continuous.comp continuous_subtype_val⟩
    refine ⟨R+ε,by linarith,F,?_,?_⟩
    · intro t h
      change (if t.val ≤ R then left t.val else right t.val) = Γ t
      rw [if_pos t.property.2]
      change Γ (Set.projIcc 0 R hR t.val) = Γ t
      rw [Set.projIcc_of_mem hR t.property]
    · intro t
      change actualDevelopment (if t.val ≤ R then left t.val else right t.val) = δ t.val
      by_cases ht : t.val ≤ R
      · rw [if_pos ht]
        have hmem : t.val ∈ Set.Icc 0 R := ⟨t.property.1,ht⟩
        change actualDevelopment (Γ (Set.projIcc 0 R hR t.val)) = δ t.val
        rw [Set.projIcc_of_mem hR hmem]
        exact hlift ⟨t.val,hmem⟩
      · rw [if_neg ht]
        have hmem : t.val ∈ Set.Icc (R-ε) (R+ε) := by
          refine ⟨?_,t.property.2⟩
          have hlt := lt_of_not_ge ht
          linarith
        change actualDevelopment (κ (Set.projIcc (R-ε) (R+ε) hεbounds t.val)) = δ t.val
        rw [Set.projIcc_of_mem hεbounds hmem]
        exact hκlift ⟨t.val,hmem⟩
  have closed_lifts_agree (R S t : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
      (ht : 0 ≤ t) (htR : t ≤ R) (htS : t ≤ S)
      (Γ : C(↥(Set.Icc (0 : ℝ) R),P)) (Λ : C(↥(Set.Icc (0 : ℝ) S),P))
      (δ : C(ℝ,H2))
      (hΓ : ∀ u, actualDevelopment (Γ u) = δ u.val)
      (hΛ : ∀ u, actualDevelopment (Λ u) = δ u.val)
      (hstart : Γ ⟨0,⟨le_rfl,hR⟩⟩ = Λ ⟨0,⟨le_rfl,hS⟩⟩) :
      Γ ⟨t,⟨ht,htR⟩⟩ = Λ ⟨t,⟨ht,htS⟩⟩ := by
    let inclR : ↥(Set.Icc (0 : ℝ) t) → ↥(Set.Icc (0 : ℝ) R) :=
      Set.inclusion (fun _ hu => ⟨hu.1,hu.2.trans htR⟩)
    let inclS : ↥(Set.Icc (0 : ℝ) t) → ↥(Set.Icc (0 : ℝ) S) :=
      Set.inclusion (fun _ hu => ⟨hu.1,hu.2.trans htS⟩)
    have hcomp : actualDevelopment ∘ (Γ ∘ inclR) = actualDevelopment ∘ (Λ ∘ inclS) := by
      funext u
      exact (hΓ (inclR u)).trans (hΛ (inclS u)).symm
    letI : PreconnectedSpace ↥(Set.Icc (0 : ℝ) t) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have heq : Γ ∘ inclR = Λ ∘ inclS :=
      (T2Space.isSeparatedMap actualDevelopment).eq_of_comp_eq
        actualDevelopment_localHomeomorph.isLocallyInjective
        (Γ.continuous.comp (continuous_inclusion _))
        (Λ.continuous.comp (continuous_inclusion _)) hcomp ⟨0,⟨le_rfl,ht⟩⟩ hstart
    exact congrFun heq ⟨t,⟨ht,le_rfl⟩⟩
  have actual_lipschitz_path_lift (δ : C(ℝ,H2)) (K : NNReal) (hδ : LipschitzWith K δ)
      (x : P) (hx : actualDevelopment x = δ 0) :
      ∃ Γ : C(Interval,P), Γ 0 = x ∧ ∀ t, actualDevelopment (Γ t) = δ t.val := by
    let LiftTo : ℝ → Prop := fun r => ∃ hr : 0 ≤ r,
      ∃ Γ : C(↥(Set.Icc (0 : ℝ) r),P), Γ ⟨0,⟨le_rfl,hr⟩⟩ = x ∧
        ∀ t, actualDevelopment (Γ t) = δ t.val
    have hzero : LiftTo 0 := by
      refine ⟨le_rfl,ContinuousMap.const _ x,rfl,?_⟩
      intro t
      have ht : t.val = 0 := le_antisymm t.property.2 t.property.1
      simpa only [ContinuousMap.const_apply,ht] using hx
    have hrestrict (r s : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (hs : LiftTo s) : LiftTo r := by
      obtain ⟨hs,Γ,hΓ0,hΓ⟩ := hs
      let incl : ↥(Set.Icc (0 : ℝ) r) → ↥(Set.Icc (0 : ℝ) s) :=
        Set.inclusion (fun _ hu => ⟨hu.1,hu.2.trans hrs⟩)
      exact ⟨hr,⟨Γ ∘ incl,Γ.continuous.comp (continuous_inclusion _)⟩,hΓ0,
        fun t => hΓ (incl t)⟩
    have hcontinue (r : ℝ) (hr : LiftTo r) : ∃ s, r < s ∧ LiftTo s := by
      obtain ⟨hr,Γ,hΓ0,hΓ⟩ := hr
      obtain ⟨s,hrs,F,hFΓ,hF⟩ := closed_lift_continues r hr Γ δ hΓ
      have hs : 0 ≤ s := hr.trans hrs.le
      refine ⟨s,hrs,hs,F,?_,hF⟩
      exact (hFΓ ⟨0,⟨le_rfl,hr⟩⟩ ⟨le_rfl,hs⟩).trans hΓ0
    let Times : Set ℝ := {r | r ∈ Set.Icc (0 : ℝ) 1 ∧ LiftTo r}
    have hTimes0 : 0 ∈ Times := ⟨⟨le_rfl,zero_le_one⟩,hzero⟩
    have hne : Times.Nonempty := ⟨0,hTimes0⟩
    have hbdd : BddAbove Times := ⟨1,fun r hr => hr.1.2⟩
    let R := sSup Times
    have hR0 : 0 ≤ R := le_csSup hbdd hTimes0
    have hR1 : R ≤ 1 := csSup_le hne (fun r hr => hr.1.2)
    have hRpos : 0 < R := by
      obtain ⟨s,hs,hsLift⟩ := hcontinue 0 hzero
      let r := min s 1
      have hr : 0 < r := lt_min hs zero_lt_one
      have hrTimes : r ∈ Times := ⟨⟨hr.le,min_le_right _ _⟩,
        hrestrict r s hr.le (min_le_left _ _) hsLift⟩
      exact hr.trans_le (le_csSup hbdd hrTimes)
    have havailable (t : ↥(Set.Ico (0 : ℝ) R)) :
        ∃ r : ℝ, ∃ hr : 0 ≤ r, t.val < r ∧
          ∃ Γ : C(↥(Set.Icc (0 : ℝ) r),P), Γ ⟨0,⟨le_rfl,hr⟩⟩ = x ∧
            ∀ u, actualDevelopment (Γ u) = δ u.val := by
      obtain ⟨r,hr,htr⟩ := exists_lt_of_lt_csSup hne t.property.2
      obtain ⟨hr0,Γ,hΓ0,hΓ⟩ := hr.2
      exact ⟨r,hr0,htr,Γ,hΓ0,hΓ⟩
    choose radius radius_nonneg radius_gt branch branch_start branch_projects using havailable
    let γ : ↥(Set.Ico (0 : ℝ) R) → P := fun t =>
      branch t ⟨t.val,⟨t.property.1,(radius_gt t).le⟩⟩
    have γprojects (t : ↥(Set.Ico (0 : ℝ) R)) : actualDevelopment (γ t) = δ t.val :=
      branch_projects t _
    have γstart : γ ⟨0,⟨le_rfl,hRpos⟩⟩ = x := branch_start _
    have γcontinuous : Continuous γ := by
      apply continuous_iff_continuousAt.mpr
      intro t
      let fixed : C(ℝ,P) := {
        toFun := fun u => branch t (Set.projIcc 0 (radius t) (radius_nonneg t) u)
        continuous_toFun := (branch t).continuous.comp
          (LipschitzWith.projIcc (radius_nonneg t)).continuous }
      have hnear : ∀ᶠ u : ↥(Set.Ico (0 : ℝ) R) in 𝓝 t, u.val < radius t :=
        (isOpen_lt continuous_subtype_val continuous_const).mem_nhds (radius_gt t)
      have hevent : γ =ᶠ[𝓝 t] (fun u : ↥(Set.Ico (0 : ℝ) R) => fixed u.val) := by
        filter_upwards [hnear] with u hu
        change branch u ⟨u.val,⟨u.property.1,(radius_gt u).le⟩⟩ =
          branch t (Set.projIcc 0 (radius t) (radius_nonneg t) u.val)
        rw [Set.projIcc_of_mem (radius_nonneg t) ⟨u.property.1,hu.le⟩]
        exact closed_lifts_agree (radius u) (radius t) u.val (radius_nonneg u)
          (radius_nonneg t) u.property.1 (radius_gt u).le hu.le (branch u) (branch t) δ
          (branch_projects u) (branch_projects t) ((branch_start u).trans (branch_start t).symm)
      exact ((fixed.continuous.comp continuous_subtype_val).continuousAt).congr hevent.symm
    obtain ⟨Γ,hΓγ,hΓ⟩ := partial_lift_endpoint_completion R hRpos K
      ⟨γ,γcontinuous⟩ δ hδ γprojects
    have hRLift : LiftTo R := ⟨hR0,Γ,
      (hΓγ ⟨0,⟨le_rfl,hRpos⟩⟩).trans γstart,hΓ⟩
    have hR_eq : R = 1 := by
      apply le_antisymm hR1
      by_contra hnot
      have hlt : R < 1 := lt_of_not_ge hnot
      obtain ⟨s,hrs,hsLift⟩ := hcontinue R hRLift
      let r := min s 1
      have hRr : R < r := lt_min hrs hlt
      have hr0 : 0 ≤ r := hR0.trans hRr.le
      have hrTimes : r ∈ Times := ⟨⟨hr0,min_le_right _ _⟩,
        hrestrict r s hr0 (min_le_left _ _) hsLift⟩
      exact (not_lt_of_ge (le_csSup hbdd hrTimes)) hRr
    obtain ⟨hr,F,hF0,hF⟩ := hrestrict 1 R zero_le_one hR_eq.ge hRLift
    exact ⟨F,hF0,hF⟩
  let q : H2 := actualDevelopment a
  have line_height (t : Interval) (y : H2) : min q.im y.im ≤
      (AffineMap.lineMap (q : ℂ) (y : ℂ) (t : ℝ)).im := by
    simp only [AffineMap.lineMap_apply_module,Complex.add_im,Complex.real_smul,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,UpperHalfPlane.coe_im]
    have h0 := t.property.1
    have h1 := t.property.2
    have hl := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (min_le_left q.im y.im))
    have hr := mul_nonneg h0 (sub_nonneg.mpr (min_le_right q.im y.im))
    nlinarith
  have line_positive (t : Interval) (y : H2) :
      0 < (AffineMap.lineMap (q : ℂ) (y : ℂ) (t : ℝ)).im :=
    (lt_min q.im_pos y.im_pos).trans_le (line_height t y)
  let lineFamily : C(Interval × H2,H2) := {
    toFun := fun ty => ⟨AffineMap.lineMap (q : ℂ) (ty.2 : ℂ) (ty.1 : ℝ),line_positive ty.1 ty.2⟩
    continuous_toFun := UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr (by
      change Continuous (fun ty : Interval × H2 =>
        AffineMap.lineMap (q : ℂ) (ty.2 : ℂ) (ty.1 : ℝ))
      simp only [AffineMap.lineMap_apply_module]
      dsimp only [Interval]
      fun_prop) }
  have lineFamily_zero (y : H2) : lineFamily (0,y) = q := by
    apply UpperHalfPlane.ext
    exact AffineMap.lineMap_apply_zero _ _
  have lineFamily_one (y : H2) : lineFamily (1,y) = y := by
    apply UpperHalfPlane.ext
    exact AffineMap.lineMap_apply_one _ _
  let clip : ℝ → Interval := Set.projIcc 0 1 zero_le_one
  let straightBase (y : H2) : C(ℝ,H2) := {
    toFun := fun t => lineFamily (clip t,y)
    continuous_toFun := lineFamily.continuous.comp
      ((LipschitzWith.projIcc zero_le_one).continuous.prodMk continuous_const) }
  have straightBase_lipschitz (y : H2) :
      LipschitzWith (nndist (q : ℂ) (y : ℂ) / Real.toNNReal (min q.im y.im)) (straightBase y) := by
    let ε := min q.im y.im
    have hε : 0 < ε := lt_min q.im_pos y.im_pos
    have hcomplex : LipschitzWith (nndist (q : ℂ) (y : ℂ))
        (fun t : ℝ => (straightBase y t : ℂ)) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      have hline := (lipschitzWith_lineMap (q : ℂ) (y : ℂ)).dist_le_mul
        (clip s : ℝ) (clip t : ℝ)
      have hc : dist (clip s : ℝ) (clip t : ℝ) ≤ dist s t := by
        have h := (LipschitzWith.projIcc zero_le_one).dist_le_mul s t
        simpa only [NNReal.coe_one,one_mul,Subtype.dist_eq] using h
      exact hline.trans (mul_le_mul_of_nonneg_left hc (NNReal.coe_nonneg _))
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have hs : ε ≤ (straightBase y s).im := line_height (clip s) y
    have ht : ε ≤ (straightBase y t).im := line_height (clip t) y
    have hsqrt : ε ≤ Real.sqrt ((straightBase y s).im * (straightBase y t).im) :=
      Real.le_sqrt_of_sq_le (by
        calc ε^2 = ε*ε := sq ε
             _ ≤ (straightBase y s).im * (straightBase y t).im :=
               mul_le_mul hs ht hε.le (straightBase y s).im_pos.le)
    calc dist (straightBase y s) (straightBase y t) ≤
          dist (straightBase y s : ℂ) (straightBase y t : ℂ) / ε :=
            ((straightBase y s).dist_le_dist_coe_div_sqrt (straightBase y t)).trans
              (div_le_div_of_nonneg_left dist_nonneg hε hsqrt)
         _ ≤ (nndist (q : ℂ) (y : ℂ) : ℝ) * dist s t / ε :=
           div_le_div_of_nonneg_right (hcomplex.dist_le_mul s t) hε.le
         _ = ((nndist (q : ℂ) (y : ℂ) / Real.toNNReal ε : NNReal) : ℝ) * dist s t := by
           rw [NNReal.coe_div,Real.coe_toNNReal _ hε.le]
           ring
  have straight_lifts (y : H2) : ∃ Γ : C(Interval,P),
      Γ 0 = a ∧ ∀ t, actualDevelopment (Γ t) = lineFamily (t,y) := by
    have h0 : actualDevelopment a = straightBase y 0 := by
      apply UpperHalfPlane.ext
      change (q : ℂ) = AffineMap.lineMap (q : ℂ) (y : ℂ)
        ((Set.projIcc 0 1 zero_le_one 0).val)
      simp only [Set.projIcc_left,Subtype.coe_mk,AffineMap.lineMap_apply_zero]
    obtain ⟨Γ,hΓ0,hΓ⟩ := actual_lipschitz_path_lift (straightBase y) _
      (straightBase_lipschitz y) a h0
    refine ⟨Γ,hΓ0,?_⟩
    intro t
    have h := hΓ t
    change actualDevelopment (Γ t) = lineFamily (Set.projIcc 0 1 zero_le_one t.val,y) at h
    rwa [Set.projIcc_of_mem zero_le_one t.property] at h
  choose liftedStraight liftedStraight_zero liftedStraight_projects using straight_lifts
  have liftedStraight_jointly_continuous :
      Continuous (fun ty : Interval × H2 => liftedStraight ty.2 ty.1) := by
    apply actualDevelopment_localHomeomorph.continuous_lift
      (T2Space.isSeparatedMap actualDevelopment) lineFamily
    · funext ty
      exact liftedStraight_projects ty.2 ty.1
    · have heq : (fun y => liftedStraight y 0) = fun _ : H2 => a := funext liftedStraight_zero
      rw [heq]
      exact continuous_const
    · intro y
      exact (liftedStraight y).continuous
  let developmentInverse : C(H2,P) := {
    toFun := fun y => liftedStraight y 1
    continuous_toFun := liftedStraight_jointly_continuous.comp
      (continuous_const.prodMk continuous_id) }
  have developmentInverse_right (y : H2) : actualDevelopment (developmentInverse y) = y := by
    change actualDevelopment (liftedStraight y 1) = y
    rw [liftedStraight_projects,lineFamily_one]
  have developmentInverse_at_q : developmentInverse q = a := by
    have hconst : ∀ s t : Interval,
        actualDevelopment (liftedStraight q s) = actualDevelopment (liftedStraight q t) := by
      intro s t
      rw [liftedStraight_projects,liftedStraight_projects]
      apply UpperHalfPlane.ext
      change AffineMap.lineMap (q : ℂ) (q : ℂ) (s : ℝ) =
        AffineMap.lineMap (q : ℂ) (q : ℂ) (t : ℝ)
      simp
    have h := (T2Space.isSeparatedMap actualDevelopment).const_of_comp
      actualDevelopment_localHomeomorph.isLocallyInjective (liftedStraight q).continuous hconst 1 0
    exact h.trans (liftedStraight_zero q)
  have developmentInverse_left (x : P) : developmentInverse (actualDevelopment x) = x := by
    have heq : actualDevelopment ∘ (developmentInverse ∘ actualDevelopment) =
        actualDevelopment ∘ id := by
      funext y
      exact developmentInverse_right _
    have h := (T2Space.isSeparatedMap actualDevelopment).eq_of_comp_eq
      actualDevelopment_localHomeomorph.isLocallyInjective
      (developmentInverse.continuous.comp actualDevelopment.continuous) continuous_id heq a
      developmentInverse_at_q
    exact congrFun h x
  let developmentHomeomorph : H2 ≃ₜ P := {
    toFun := developmentInverse
    invFun := actualDevelopment
    left_inv := developmentInverse_right
    right_inv := developmentInverse_left
    continuous_toFun := developmentInverse.continuous
    continuous_invFun := actualDevelopment.continuous }
  refine ⟨developmentHomeomorph.symm,?_⟩
  intro x
  obtain ⟨U,T,hU,hxU,hUi,hform⟩ := actualDevelopment_local_formula x
  refine ⟨U,hU,hxU,?_⟩
  intro y hy z hz
  change dist (actualProjection y) (actualProjection z) =
    dist (actualDevelopment y) (actualDevelopment z)
  rw [hform y hy,hform z hz,T.isometry.dist_eq]
  exact (chart_spec x).2 y (hUi hy) z (hUi hz)

end CurveComplex.Hyperbolic
