import RegionalWeightedMovieDefinitions
import CurveComplexGenusTwo.Topology.ArcTrim.SupportedStrictDiskEnlargementStatement
import CurveComplexGenusTwo.Topology.Smoothing.MarkedIntervalCrosscutChartProof

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open CurveComplex.BranchedDoubleCover

private theorem affine_parameter_range (s t : Interval) :
    range (intervalAffine s t) = uIcc s t := by
  have hcont : Continuous (intervalAffine s t) := (intervalSegment s t).continuous
  have hs : s ∈ range (intervalAffine s t) := ⟨0, by simp [intervalAffine]⟩
  have ht : t ∈ range (intervalAffine s t) := ⟨1, by simp [intervalAffine]⟩
  apply Set.Subset.antisymm
  · rintro x ⟨q,rfl⟩
    rcases le_total s t with hst | hts
    · simpa [uIcc_of_le hst] using intervalAffine_mem_Icc hst q
    · have he : intervalAffine s t q = intervalAffine t s (unitInterval.symm q) := by
        apply Subtype.ext
        simp [intervalAffine, unitInterval.symm]
        ring
      rw [he, uIcc_of_ge hts]
      exact intervalAffine_mem_Icc hts _
  · exact (isPreconnected_range hcont).ordConnected.uIcc_subset hs ht

private theorem affine_subarc_range {X : Type*} [TopologicalSpace X]
    (a f : C(Interval,X)) (s t : Interval)
    (hf : ∀ q, f q = a (intervalAffine s t q)) :
    range f = a '' uIcc s t := by
  have he : (f : Interval → X) = a ∘ intervalAffine s t := funext hf
  rw [he, Set.range_comp, affine_parameter_range]

private theorem padded_interval_remainder {X : Type*} [TopologicalSpace X] [T2Space X]
    (a : C(Interval,X)) (ha : IsEmbedding a)
    (u z : Interval) (hu : 0 < u) (huz : u < z) (hz : z < 1)
    (V D : Set X) (hV : IsOpen V) (hcore : a '' Icc u z ⊆ V)
    (hD : D ∩ range a = a '' Icc u z) :
    ∃ A B : Interval, ∃ K : Set X,
      0 < A ∧ A < u ∧ z < B ∧ B < 1 ∧
      a '' Icc A B ⊆ V ∧ IsCompact K ∧
      range a = a '' Ioo A B ∪ K ∧
      Disjoint (a '' Icc u z) K ∧ Disjoint D K := by
  have hpre : IsOpen (a ⁻¹' V) := hV.preimage a.continuous
  have huV : u ∈ a ⁻¹' V := hcore ⟨u,⟨le_rfl,huz.le⟩,rfl⟩
  have hzV : z ∈ a ⁻¹' V := hcore ⟨z,⟨huz.le,le_rfl⟩,rfl⟩
  obtain ⟨l,r,hur,hleft⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0,hu⟩ ⟨1,huz.trans hz⟩).mp
      (hpre.mem_nhds huV)
  obtain ⟨l',r',hzr,hright⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0,hu.trans huz⟩ ⟨1,hz⟩).mp
      (hpre.mem_nhds hzV)
  obtain ⟨A,hA⟩ := exists_between (max_lt hu hur.1)
  obtain ⟨B,hB⟩ := exists_between (lt_min hz hzr.2)
  have hA0 : (0 : Interval) < A := (le_max_left _ _).trans_lt hA.1
  have hlA : l < A := (le_max_right _ _).trans_lt hA.1
  have hB1 : B < (1 : Interval) := hB.2.trans_le (min_le_left _ _)
  have hBr : B < r' := hB.2.trans_le (min_le_right _ _)
  have hpad : a '' Icc A B ⊆ V := by
    rintro y ⟨q,hq,rfl⟩
    by_cases hqu : q < u
    · exact hleft ⟨hlA.trans_le hq.1,hqu.trans hur.2⟩
    · by_cases hzq : z < q
      · exact hright ⟨hzr.1.trans hzq,hq.2.trans_lt hBr⟩
      · exact hcore ⟨q,⟨le_of_not_gt hqu,le_of_not_gt hzq⟩,rfl⟩
  let K : Set X := a '' (Ioo A B)ᶜ
  have hK : IsCompact K := isOpen_Ioo.isClosed_compl.isCompact.image a.continuous
  have hclear : Disjoint (a '' Icc u z) K := by
    apply disjoint_left.mpr
    rintro y ⟨q,hq,rfl⟩ ⟨t,ht,he⟩
    have heq : t = q := ha.injective he
    exact ht (heq.symm ▸ ⟨hA.2.trans_le hq.1,hq.2.trans_lt hB.1⟩)
  refine ⟨A,B,K,hA0,hA.2,hB.1,hB1,hpad,hK,?_,hclear,?_⟩
  · ext y
    constructor
    · rintro ⟨q,rfl⟩
      by_cases hq : q ∈ Ioo A B
      · exact Or.inl ⟨q,hq,rfl⟩
      · exact Or.inr ⟨q,hq,rfl⟩
    · rintro (⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩) <;> exact ⟨q,rfl⟩
  · apply disjoint_left.mpr
    intro y hyD hyK
    have hya : y ∈ range a := image_subset_range _ _ hyK
    exact disjoint_left.mp hclear (hD ▸ ⟨hyD,hya⟩) hyK

#print axioms affine_parameter_range
#print axioms affine_subarc_range
#print axioms padded_interval_remainder

private theorem proper_endpoint_parameter_interior {S : Type*} [TopologicalSpace S]
    (F B : Set S) (hBF : B ⊆ frontier F) (a : C(Interval,↥F))
    (hzero : (a 0).val ∈ B) (hone : (a 1).val ∈ B)
    (t : Interval) (ht : (a t).val ∉ frontier F) :
    0 < t ∧ t < 1 := by
  constructor
  · apply bot_lt_iff_ne_bot.mpr
    intro he
    exact ht (he.symm ▸ hBF hzero)
  · apply lt_top_iff_ne_top.mpr
    intro he
    exact ht (he.symm ▸ hBF hone)

#print axioms proper_endpoint_parameter_interior

private theorem relative_interior_open_support {S : Type*} [TopologicalSpace S]
    (F : Set S) (O : Set ↥F) (hO : IsOpen O)
    (hinside : ∀ y ∈ O, y.val ∈ interior F) :
    ∃ W : Set S, IsOpen W ∧ W ⊆ interior F ∧
      Subtype.val ⁻¹' W = O := by
  obtain ⟨U,hU,hUO⟩ := isOpen_induced_iff.mp hO
  refine ⟨U ∩ interior F,hU.inter isOpen_interior,inter_subset_right,?_⟩
  ext y
  constructor
  · intro hy
    exact hUO ▸ hy.1
  · intro hy
    have hyU : y ∈ Subtype.val ⁻¹' U := hUO.symm ▸ hy
    exact ⟨hyU,hinside y hy⟩

private theorem embedded_disk_interior_chart {S : Type} [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (e : C(Metric.closedBall (0 : Plane) 1,S)) (he : IsEmbedding e) :
    ∃ E : OpenPartialHomeomorph S Plane,
      E.source = interior (range e) ∧ E.target = Metric.ball (0 : Plane) 1 ∧
      ∀ z (hz : z ∈ Metric.ball (0 : Plane) 1),
        E.symm z = e ⟨z,Metric.ball_subset_closedBall hz⟩ := by
  classical
  let B := Metric.ball (0 : Plane) 1
  let incl : B → Metric.closedBall (0 : Plane) 1 :=
    fun z => ⟨z.val,Metric.ball_subset_closedBall z.property⟩
  have hi : IsEmbedding incl :=
    Topology.IsEmbedding.subtypeVal.codRestrict _ _
  let f : B → S := e ∘ incl
  have hf : IsEmbedding f := he.comp hi
  have hr : range f = interior (range e) := by
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq e he]
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨incl z,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z.val,hz⟩,rfl⟩
  have hfo : IsOpenEmbedding f := ⟨hf,hr.symm ▸ isOpen_interior⟩
  letI : Nonempty B := ⟨⟨0,by simp [B]⟩⟩
  let G := hfo.toOpenPartialHomeomorph f
  let J := (Metric.isOpen_ball : IsOpen B).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : B → Plane)
  let E := G.symm.trans J
  have hEs : E.source = interior (range e) := by
    simp only [E,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
      G,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
      J,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
    exact hr
  have hEt : E.target = B := by
    simp only [E,OpenPartialHomeomorph.trans_target,OpenPartialHomeomorph.symm_target,
      G,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      J,Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,preimage_univ,inter_univ,
      Subtype.range_val]
  refine ⟨E,hEs,hEt,?_⟩
  intro z hz
  change G (J.symm z) = _
  change f (J.symm z) = _
  have hJt : J.target = B := by simp [J]
  have hj : (J.symm z).val = z := J.right_inv (hJt.symm ▸ hz)
  change e (incl (J.symm z)) = _
  congr 1
  exact Subtype.ext hj

private theorem disk_chart_in_relative_support {S : Type} [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (O : Set ↥F) (hO : IsOpen O)
    (hinside : ∀ y ∈ O, y.val ∈ interior F)
    (d : C(Metric.closedBall (0 : Plane) 1,↥F)) (hd : IsEmbedding d)
    (hdO : range d ⊆ O) :
    ∃ E : OpenPartialHomeomorph S Plane,
      (∀ y ∈ range d, y.val ∈ E.source) ∧
      closure E.source ⊆ Subtype.val '' O ∩ interior F ∧
      E.target = Metric.ball (0 : Plane) 1 := by
  obtain ⟨W,hW,hWF,hWO⟩ := relative_interior_open_support F O hO hinside
  let ds : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
  have hds : IsEmbedding ds := IsEmbedding.subtypeVal.comp hd
  have hdsW : range ds ⊆ W := by
    rintro y ⟨z,rfl⟩
    change d z ∈ Subtype.val ⁻¹' W
    rw [hWO]
    exact hdO (mem_range_self z)
  obtain ⟨_,e,he,hde,heW,_,_,_⟩ :=
    CurveComplex.LocalSurgery.exists_supported_strict_disk_enlargement ds hds W hW hdsW
  obtain ⟨E,hEs,hEt,_⟩ := embedded_disk_interior_chart e he
  refine ⟨E,?_,?_,hEt⟩
  · rintro y ⟨z,rfl⟩
    rw [hEs]
    exact hde (mem_range_self z)
  · rw [hEs]
    have hclosure : closure (interior (range e)) ⊆ range e :=
      closure_minimal interior_subset (isCompact_range e.continuous).isClosed
    intro y hy
    have hyW := heW (hclosure hy)
    have hyF := hWF hyW
    refine ⟨⟨⟨y,interior_subset hyF⟩,?_,rfl⟩,hyF⟩
    exact hWO ▸ hyW

#print axioms relative_interior_open_support
#print axioms embedded_disk_interior_chart
#print axioms disk_chart_in_relative_support

private theorem clipped_interval_image {X : Type*} (a : Interval → X) (s t : Interval) :
    (a ∘ Set.projIcc 0 1 zero_le_one) '' Icc s.val t.val = a '' Icc s t := by
  ext y
  constructor
  · rintro ⟨q,hq,rfl⟩
    have hq01 : q ∈ Icc (0 : ℝ) 1 :=
      ⟨s.property.1.trans hq.1,hq.2.trans t.property.2⟩
    refine ⟨⟨q,hq01⟩,hq,?_⟩
    simp only [Function.comp_apply,projIcc_of_mem zero_le_one hq01]
  · rintro ⟨q,hq,rfl⟩
    exact ⟨q.val,hq,by simp [projIcc_of_mem zero_le_one q.property]⟩

private theorem relative_subarc_axis_chart {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (a : C(Interval,↥F)) (ha : IsEmbedding a)
    (s t : Interval) (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (e : OpenPartialHomeomorph S Plane)
    (W : Set S) (hW : IsOpen W)
    (hsub : ∀ y ∈ a '' Icc s t, y.val ∈ W ∩ e.source) :
    ∃ E : OpenPartialHomeomorph S Plane,
      E.source ⊆ W ∩ e.source ∧ Plane.closedSquare 0 1 ⊆ E.target ∧
      (∀ y ∈ a '' Icc s t, y.val ∈ E.source) ∧
      E (a s).val = Plane.mk (-1) 0 ∧ E (a t).val = Plane.mk 1 0 ∧
      (∀ y ∈ E.source, y ∈ range (fun q => (a q).val) ↔ E y 1 = 0) ∧
      {y : ↥F | y.val ∈ E.source ∧ E y.val ∈ Plane.closedSquare 0 1} ∩ range a =
        a '' Icc s t := by
  let γ : Interval → S := fun q => (a q).val
  have hγ : Continuous γ := continuous_subtype_val.comp a.continuous
  have hγinj : Function.Injective γ := fun q r h => ha.injective (Subtype.ext h)
  have hcoll : ∀ q r, γ q = γ r → q = r ∨
      (q = (0 : Interval) ∧ r = (1 : Interval)) ∨
      (q = (1 : Interval) ∧ r = (0 : Interval)) :=
    fun q r h => Or.inl (hγinj h)
  have hclip : (γ ∘ projIcc 0 1 zero_le_one) '' Icc s.val t.val =
      Subtype.val '' (a '' Icc s t) := by
    rw [clipped_interval_image, image_image]
  have hsub' : (γ ∘ projIcc 0 1 zero_le_one) '' Icc s.val t.val ⊆ W ∩ e.source := by
    rw [hclip]
    rintro y ⟨z,hz,rfl⟩
    exact hsub z hz
  obtain ⟨E,hEW,hEsquare,hEcore,hEs,hEt,hEaxis,hEtrace⟩ :=
    actual_interval_subarc_crosscut_chart γ hγ hcoll s.val t.val hs hst ht e W hW hsub'
  have hzeros : (γ ∘ projIcc 0 1 zero_le_one) s.val = (a s).val := by
    simp [γ,projIcc_of_mem zero_le_one s.property]
  have hones : (γ ∘ projIcc 0 1 zero_le_one) t.val = (a t).val := by
    simp [γ,projIcc_of_mem zero_le_one t.property]
  refine ⟨E,hEW,hEsquare,?_,hzeros ▸ hEs,hones ▸ hEt,hEaxis,?_⟩
  · intro y hy
    apply hEcore
    rw [hclip]
    exact ⟨y,hy,rfl⟩
  · ext y
    constructor
    · intro hy
      have hys : y.val ∈ Subtype.val '' (a '' Icc s t) := by
        rw [← hclip,← hEtrace]
        rcases hy.2 with ⟨q,hq⟩
        exact ⟨hy.1,⟨q,congrArg Subtype.val hq⟩⟩
      obtain ⟨z,hz,hzy⟩ := hys
      exact (Subtype.ext hzy : z = y) ▸ hz
    · intro hy
      have hys : y.val ∈ {x | x ∈ E.source ∧ E x ∈ Plane.closedSquare 0 1} ∩ range γ := by
        rw [hEtrace,hclip]
        exact ⟨y,hy,rfl⟩
      rcases hy with ⟨q,hq,hqy⟩
      exact ⟨hys.1,⟨q,hqy⟩⟩

#print axioms clipped_interval_image
#print axioms relative_subarc_axis_chart
