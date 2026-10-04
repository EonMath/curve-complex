import OrdinarySignedGeometry
import CurveComplexGenusTwo.Topology.ActualOrdinaryGuidingGeometry.OrdinaryGuidingRedraw
import CurveComplexGenusTwo.Topology.ActualOrdinaryGuidingGeometry.OrdinarySupportedMovie
import RegionalWeightedFanScaffold
import RegionalWeightedMovieDefinitions
import CurveComplexGenusTwo.Topology.ArcTrim.SupportedStrictDiskEnlargementStatement
import CurveComplexGenusTwo.Topology.Smoothing.MarkedIntervalCrosscutChartProof

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open CurveComplex.BranchedDoubleCover
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

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

/-- M1/M2 (ordinary): exactly the existing local hgeometry movie/count interface. M0 is a proof dependency, not a final-movie assumption. -/
theorem regional_ordinary_disk_supported_movie_geometry
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ (ι : Type) [Fintype ι] (r : ι → IntrinsicEssentialArc)
      (α : IntrinsicEssentialArc),
      FamilyInvariant (fun i => (r i).val.val) α.val.val →
      (∀ i j : Option ι, i ≠ j →
        RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
          (augmented (fun i => (r i).val.val) α.val.val i)
          (augmented (fun i => (r i).val.val) α.val.val j)) →
      ∀ v w : ι, v ≠ w →
      ∀ d : PairedBigonDisk F {y | y.val ∈ frontier F} (r v).val.val (r w).val.val,
      ∀ V : Set ↥F, IsOpen V → range d.disk ⊆ V →
        (∀ y ∈ closure V, y.val ∈ interior F) →
        Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ boundaryCircle}) →
        let C₀ : Set ↥F := {d.first 0,d.first 1}
        let removed := fun j : ι => ((range d.first \ C₀) ∩ range (r j).val.val).ncard
        let guiding := fun j : ι => ((range d.second \ C₀) ∩ range (r j).val.val).ncard
        let offset := fun j : ι =>
          ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard +
            (C₀ ∩ range (r j).val.val).ncard
        (∑ j : ι, if j ≠ v ∧ j ≠ w then guiding j else 0) ≤
          (∑ j : ι, if j ≠ v ∧ j ≠ w then removed j else 0) →
        ∃ H : AmbientIsotopy ↥F,
      (∀ t y, y ∉ V → H.map (t,y) = y) ∧
      (∀ t y, y.val ∈ frontier F → H.map (t,y) = y) ∧
      (∀ j, j ≠ v →
        (H.finalMap '' range (r v).val.val ∩ range (r j).val.val).Finite) ∧
      (H.finalMap '' range (r v).val.val ∩ range α.val.val).Finite ∧
      (∀ j, j ≠ v → j ≠ w →
        (H.finalMap '' range (r v).val.val ∩ range (r j).val.val).ncard ≤
          guiding j + offset j) ∧
      (H.finalMap '' range (r v).val.val ∩ range (r w).val.val).ncard + 2 ≤
        (range (r v).val.val ∩ range (r w).val.val).ncard := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV hVinside havoid
    C₀ removed guiding offset hcheap
  have hBF : boundaryCircle ⊆ frontier F := by
    dsimp only [boundaryCircle]
    rw [hfrontier]
    exact Set.subset_union_left
  have hcutStart : (d.first 0).val = ((r v).val.val d.aStart).val := by
    simpa [intervalAffine] using congrArg Subtype.val (d.first_eq 0)
  have hcutFinish : (d.first 1).val = ((r v).val.val d.aFinish).val := by
    simpa [intervalAffine] using congrArg Subtype.val (d.first_eq 1)
  have hstartInterior : 0 < d.aStart ∧ d.aStart < 1 :=
    proper_endpoint_parameter_interior F boundaryCircle hBF (r v).val.val
      (r v).val.property.2.1 (r v).val.property.2.2.1 d.aStart
      (hcutStart ▸ d.corners_off_frontier.1)
  have hfinishInterior : 0 < d.aFinish ∧ d.aFinish < 1 :=
    proper_endpoint_parameter_interior F boundaryCircle hBF (r v).val.val
      (r v).val.property.2.1 (r v).val.property.2.2.1 d.aFinish
      (hcutFinish ▸ d.corners_off_frontier.2)
  let u := min d.aStart d.aFinish
  let z := max d.aStart d.aFinish
  have hu : 0 < u := lt_min hstartInterior.1 hfinishInterior.1
  have huz : u < z := min_lt_max.mpr d.a_distinct
  have hz : z < 1 := max_lt hstartInterior.2 hfinishInterior.2
  have hfirstRange : range d.first = (r v).val.val '' Icc u z :=
    affine_subarc_range (r v).val.val d.first d.aStart d.aFinish d.first_eq
  have hcoreV : (r v).val.val '' Icc u z ⊆ V := by
    rw [← hfirstRange]
    intro y hy
    exact hdV ((d.whole_first.symm ▸ hy).1)
  have hwhole : range d.disk ∩ range (r v).val.val = (r v).val.val '' Icc u z :=
    d.whole_first.trans hfirstRange
  obtain ⟨A,B,K,hA0,hAu,hzB,hB1,hpad,hK,hdecomp,hcoreK,hdK⟩ :=
    padded_interval_remainder (r v).val.val (r v).val.property.1 u z hu huz hz
      V (range d.disk) hV hcoreV hwhole
  let O := V \ K
  have hO : IsOpen O := hV.sdiff hK.isClosed
  have hdO : range d.disk ⊆ O := by
    intro y hy
    exact ⟨hdV hy,fun hk => disjoint_left.mp hdK hy hk⟩
  have hOinside : ∀ y ∈ O, y.val ∈ interior F := by
    intro y hy
    exact hVinside y (subset_closure hy.1)
  obtain ⟨Edisk,hdEdisk,hEdiskClosure,hEdiskTarget⟩ :=
    disk_chart_in_relative_support F O hO hOinside d.disk d.disk_embedded hdO
  have hEdiskInV : ∀ y : ↥F, y.val ∈ closure Edisk.source → y ∈ V := by
    intro y hy
    obtain ⟨z,hz,hzy⟩ := (hEdiskClosure hy).1
    have he : z = y := Subtype.ext hzy
    exact he ▸ hz.1
  have hEdiskTailClear : Disjoint {y : ↥F | y.val ∈ closure Edisk.source} K := by
    apply disjoint_left.mpr
    intro y hy hk
    obtain ⟨z,hz,hzy⟩ := (hEdiskClosure hy).1
    have he : z = y := Subtype.ext hzy
    exact hz.2 (he.symm ▸ hk)
  have hguidingStart : (d.second 0).val = ((r w).val.val d.bStart).val := by
    simpa [intervalAffine] using congrArg Subtype.val (d.second_eq 0)
  have hguidingFinish : (d.second 1).val = ((r w).val.val d.bFinish).val := by
    simpa [intervalAffine] using congrArg Subtype.val (d.second_eq 1)
  have hsecondZeroOff : (d.second 0).val ∉ frontier F :=
    d.zero_eq ▸ d.corners_off_frontier.1
  have hsecondOneOff : (d.second 1).val ∉ frontier F :=
    d.one_eq ▸ d.corners_off_frontier.2
  have hbstart : 0 < d.bStart ∧ d.bStart < 1 :=
    proper_endpoint_parameter_interior F boundaryCircle hBF (r w).val.val
      (r w).val.property.2.1 (r w).val.property.2.2.1 d.bStart
      (hguidingStart ▸ hsecondZeroOff)
  have hbfinish : 0 < d.bFinish ∧ d.bFinish < 1 :=
    proper_endpoint_parameter_interior F boundaryCircle hBF (r w).val.val
      (r w).val.property.2.1 (r w).val.property.2.2.1 d.bFinish
      (hguidingFinish ▸ hsecondOneOff)
  let gu := min d.bStart d.bFinish
  let gz := max d.bStart d.bFinish
  have hgu : 0 < gu := lt_min hbstart.1 hbfinish.1
  have hggap : gu < gz := min_lt_max.mpr d.b_distinct
  have hgz : gz < 1 := max_lt hbstart.2 hbfinish.2
  have hsecondRange : range d.second = (r w).val.val '' Icc gu gz :=
    affine_subarc_range (r w).val.val d.second d.bStart d.bFinish d.second_eq
  have hguidingInChart : ∀ y ∈ (r w).val.val '' Icc gu gz,
      y.val ∈ Edisk.source ∩ Edisk.source := by
    intro y hy
    have hys : y ∈ range d.second := hsecondRange.symm ▸ hy
    have hyd : y ∈ range d.disk := (d.whole_second.symm ▸ hys).1
    exact ⟨hdEdisk y hyd,hdEdisk y hyd⟩
  obtain ⟨Eguide,hGuideSource,hGuideSquare,hGuideCore,hGuideZero,hGuideOne,
    hGuideAxis,hGuideTrace⟩ :=
    relative_subarc_axis_chart F (r w).val.val (r w).val.property.1 gu gz
      hgu hggap hgz Edisk Edisk.source Edisk.open_source hguidingInChart
  have hGuideInterior : Eguide.source ⊆ interior F := by
    intro y hy
    exact (hEdiskClosure (subset_closure (hGuideSource hy).1)).2
  have hGuideSupportV : ∀ y : ↥F, y.val ∈ Eguide.source → y ∈ V := by
    intro y hy
    exact hEdiskInV y (subset_closure (hGuideSource hy).1)
  have hGuideTailClear : Disjoint {y : ↥F | y.val ∈ Eguide.source} K := by
    apply disjoint_left.mpr
    intro y hy hk
    exact disjoint_left.mp hEdiskTailClear
      (subset_closure (hGuideSource hy).1) hk
  obtain ⟨⟨fan⟩,hfirstObserver,hsecondObserver,hpartition⟩ :=
    regional_paired_disk_finite_fan_carrier S g hg hS x R hR htarget F
      hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
      ι r α hinv hcross v w hvw d V hV hdV hVinside havoid
  obtain ⟨D⟩ := regional_ordinary_signed_contact_corner_families S g hg hS x R hR htarget F
    hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
    ι r α hinv hcross v w hvw d V hV hdV hVinside havoid hcheap
    A B K hA0 hAu hzB hB1 hpad hK hdecomp hcoreK hdK Edisk Eguide
    hdEdisk hEdiskClosure hEdiskTarget hGuideSource hGuideSquare hGuideCore
    hGuideZero hGuideOne hGuideAxis hGuideTrace fan
  let f := augmented (fun i => (r i).val.val) α.val.val
  obtain ⟨τ,hτ0,hτε,gap,hgap,n,hn,hnSource,hnmeet,hnguide,hnpieces,hnfinite,hnbound⟩ :=
    regional_ordinary_guiding_redraw_from_signed_pieces F f v w d A B Edisk Eguide
      (fun y hy => (hGuideSource hy).1) hGuideInterior hGuideAxis (r v).val.property.1 D
  have hl0 : 0 < D.l := hA0.trans D.cuts.1
  have hlr : D.l < D.r := D.cuts.2.1.trans (D.cuts.2.2.1.trans D.cuts.2.2.2.1)
  have hr1 : D.r < 1 := D.cuts.2.2.2.2.trans hB1
  have hEdiskV : closure Edisk.source ⊆ Subtype.val '' V ∩ interior F := by
    intro y hy
    obtain ⟨⟨z,hz,hzy⟩,hyF⟩ := hEdiskClosure hy
    exact ⟨⟨z,hz.1,hzy⟩,hyF⟩
  obtain ⟨H,hHV,hHT,hHtails,hHrange,hH0,hH1⟩ :=
    regional_proper_interval_redraw_supported_movie S F V Edisk hEdiskTarget hEdiskV
      (r v).val.val (r v).val.property.1 (hBF (r v).val.property.2.1)
      (hBF (r v).val.property.2.2.1) D.l D.r hl0 hlr hr1 n hn
      (union_subset D.old_in_disk hnSource) hnmeet
  let T := (r v).val.val '' Iic D.l ∪ (r v).val.val '' Ici D.r
  have hTold : T ⊆ range (r v).val.val :=
    union_subset (image_subset_range _ _) (image_subset_range _ _)
  have hTfirst : Disjoint T (range d.first) := by
    apply disjoint_left.mpr
    intro y hy hyfirst
    rw [hfirstRange] at hyfirst
    obtain ⟨q,hq,rfl⟩ := hyfirst
    rcases hy with ⟨t,ht,he⟩ | ⟨t,ht,he⟩
    · have heq : t = q := (r v).val.property.1.injective he
      have hqu : q < u := (heq ▸ ht).trans_lt D.cuts.2.1
      exact (not_lt_of_ge hq.1) hqu
    · have heq : t = q := (r v).val.property.1.injective he
      have hzq : z < q := D.cuts.2.2.2.1.trans_le (heq ▸ ht)
      exact (not_lt_of_ge hq.2) hzq
  have hToutside : T ⊆ range (r v).val.val \ range d.first :=
    fun y hy => ⟨hTold hy,fun hf => disjoint_left.mp hTfirst hy hf⟩
  have hWholeFinite : ∀ j, j ≠ v →
      (range (r v).val.val ∩ range (r j).val.val).Finite :=
    fun j hj => hinv.1 v j hj.symm
  have hTailFinite : ∀ j, j ≠ v → (T ∩ range (r j).val.val).Finite :=
    fun j hj => (hWholeFinite j hj).subset (inter_subset_inter_left _ hTold)
  have hTailObserver : (T ∩ range α.val.val).Finite := by
    have hf : (range (r v).val.val ∩ range α.val.val).Finite := by
      simpa only [inter_comm] using hinv.2.2.2.2 v
    exact hf.subset (inter_subset_inter_left _ hTold)
  have hFinal : H.finalMap '' range (r v).val.val = T ∪ range n := hHrange
  refine ⟨H,hHV,hHT,?_,?_,?_,?_⟩
  · intro j hj
    rw [hFinal,union_inter_distrib_right]
    exact (hTailFinite j hj).union (hnfinite (some j) (by simpa using hj))
  · rw [hFinal,union_inter_distrib_right]
    exact hTailObserver.union (hnfinite none (by simp))
  · intro j hjv hjw
    have hOffsetFinite : ((range (r v).val.val \ range d.first) ∩
        range (r j).val.val).Finite :=
      (hWholeFinite j hjv).subset (fun y hy => ⟨hy.1.1,hy.2⟩)
    have hTailBound : (T ∩ range (r j).val.val).ncard ≤
        ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard :=
      ncard_le_ncard (inter_subset_inter_left _ hToutside) hOffsetFinite
    have hNewBound : (range n ∩ range (r j).val.val).ncard ≤
        guiding j + (C₀ ∩ range (r j).val.val).ncard :=
      hnbound (some j) (by simpa using hjv) (by simpa using hjw)
    have hUnionBound := ncard_union_le (T ∩ range (r j).val.val)
      (range n ∩ range (r j).val.val)
    rw [hFinal,union_inter_distrib_right]
    calc
      _ ≤ (T ∩ range (r j).val.val).ncard + (range n ∩ range (r j).val.val).ncard :=
        hUnionBound
      _ ≤ ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard +
          (guiding j + (C₀ ∩ range (r j).val.val).ncard) :=
        Nat.add_le_add hTailBound hNewBound
      _ = guiding j + offset j := by dsimp only [offset]; omega
  · have hCutGuide : range d.first ∩ range (r w).val.val = C₀ := by
      apply Subset.antisymm
      · intro y hy
        have hyd : y ∈ range d.disk := (d.whole_first.symm ▸ hy.1).1
        have hys : y ∈ range d.second := d.whole_second ▸ ⟨hyd,hy.2⟩
        change y ∈ ({d.first 0,d.first 1} : Set ↥F)
        exact d.sides_inter ▸ ⟨hy.1,hys⟩
      · intro y hy
        have hys : y ∈ range d.first ∩ range d.second := d.sides_inter.symm ▸ hy
        refine ⟨hys.1,?_⟩
        obtain ⟨q,hq⟩ := hys.2
        exact ⟨intervalAffine d.bStart d.bFinish q,(d.second_eq q).symm.trans hq⟩
    let O := (range (r v).val.val \ range d.first) ∩ range (r w).val.val
    have hOFinite : O.Finite :=
      (hWholeFinite w hvw.symm).subset (fun y hy => ⟨hy.1.1,hy.2⟩)
    have hOldPartition : range (r v).val.val ∩ range (r w).val.val = O ∪ C₀ := by
      ext y
      constructor
      · intro hy
        by_cases hyfirst : y ∈ range d.first
        · exact Or.inr (hCutGuide ▸ ⟨hyfirst,hy.2⟩)
        · exact Or.inl ⟨⟨hy.1,hyfirst⟩,hy.2⟩
      · rintro (hy | hy)
        · exact ⟨hy.1.1,hy.2⟩
        · have hh : y ∈ range d.first ∩ range (r w).val.val := hCutGuide.symm ▸ hy
          exact ⟨(d.whole_first.symm ▸ hh.1).2,hh.2⟩
    have hOC : Disjoint O C₀ := by
      apply disjoint_left.mpr
      intro y hy hyC
      exact hy.1.2 (hCutGuide.symm ▸ hyC).1
    have hOldCount : (range (r v).val.val ∩ range (r w).val.val).ncard = O.ncard + 2 := by
      rw [hOldPartition,ncard_union_eq hOC hOFinite (by dsimp [C₀]; exact (finite_singleton _).insert _)]
      rw [show C₀.ncard = 2 from ncard_pair d.corners_distinct]
    have hNewGuide : range n ∩ range (r w).val.val = ∅ :=
      disjoint_iff_inter_eq_empty.mp hnguide
    have hFinalBound : (H.finalMap '' range (r v).val.val ∩ range (r w).val.val).ncard ≤ O.ncard := by
      rw [hFinal,union_inter_distrib_right,hNewGuide,union_empty]
      exact ncard_le_ncard (inter_subset_inter_left _ hToutside) hOFinite
    omega
