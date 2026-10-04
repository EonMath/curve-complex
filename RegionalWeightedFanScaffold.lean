import RegionalWeightedMovieDefinitions
import RegionalOrdinaryFanWindowScaffold
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteScalarNegativeIntervals
import CurveComplexGenusTwo.Topology.CapBandGeometry.DiskOpen
open Set Metric Topology CurveComplex Schoenflies RegionalTotalDecrease RegionalWeightedMovies
set_option maxHeartbeats 2200000

private theorem closed_interval_set_finite_frontier_pieces
    (A : Set Interval) (hA : IsClosed A) (hfront : (frontier A).Finite) :
    ∃ pieces : Finset (Interval × Interval),
      (∀ lr ∈ pieces, lr.1 ≤ lr.2) ∧ A = ⋃ lr ∈ pieces, Icc lr.1 lr.2 := by
  classical
  rcases A.eq_empty_or_nonempty with hEmpty | hNonempty
  · exact ⟨∅,by simp,by simp [hEmpty]⟩
  rcases Aᶜ.eq_empty_or_nonempty with hFull | hComplement
  · have hAFull : A = univ := by
      ext t
      simp only [mem_univ,iff_true]
      by_contra hn
      have ht : t ∈ (∅ : Set Interval) := hFull ▸ hn
      exact ht.elim
    exact ⟨{(0,1)},by simp,by simpa [hAFull] using unitInterval.univ_eq_Icc⟩
  let scalar : C(Interval,ℝ) := ⟨fun t => infDist t A - infDist t Aᶜ,
    (continuous_infDist_pt A).sub (continuous_infDist_pt Aᶜ)⟩
  have hscalar : ∀ t, scalar t ≤ 0 ↔ t ∈ A := by
    intro t
    constructor
    · intro h
      by_contra ht
      have hzero := infDist_zero_of_mem (show t ∈ Aᶜ from ht)
      have hpos := (hA.notMem_iff_infDist_pos hNonempty).mp ht
      change infDist t A - infDist t Aᶜ ≤ 0 at h
      rw [hzero] at h
      linarith
    · intro ht
      change infDist t A - infDist t Aᶜ ≤ 0
      rw [infDist_zero_of_mem ht]
      linarith [show 0 ≤ infDist t Aᶜ from infDist_nonneg]
  have hzeros : (scalar ⁻¹' {0}).Finite := by
    apply hfront.subset
    intro t ht
    change scalar t = 0 at ht
    have htA := (hscalar t).mp ht.le
    rw [frontier_eq_closure_inter_closure]
    refine ⟨hA.closure_eq.symm ▸ htA,?_⟩
    apply (mem_closure_iff_infDist_zero hComplement).mpr
    change infDist t A - infDist t Aᶜ = 0 at ht
    rw [infDist_zero_of_mem htA] at ht
    linarith
  obtain ⟨m,mesh,negative,hmono,h0,h1,hnodes,hno,hnegative,hcover⟩ :=
    CurveComplex.HyperellipticModel.actual_finite_scalar_negative_intervals scalar hzeros
  let intervals : Finset (Interval × Interval) :=
    (Finset.univ.filter negative).image (fun j : Fin (m+1) => (mesh j.castSucc,mesh j.succ))
  let points : Finset (Interval × Interval) := hzeros.toFinset.image (fun t => (t,t))
  refine ⟨intervals ∪ points,?_,?_⟩
  · intro lr hlr
    rcases Finset.mem_union.mp hlr with hi | hp
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact hmono.monotone (by change j.val ≤ j.val + 1; omega)
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      exact le_rfl
  · ext t
    constructor
    · intro ht
      rcases (hcover t).mp ((hscalar t).mpr ht) with hz | ⟨j,hj,ht⟩
      · refine mem_iUnion.mpr ⟨(t,t),mem_iUnion.mpr ⟨Finset.mem_union_right _ ?_,?_⟩⟩
        · exact Finset.mem_image.mpr ⟨t,hzeros.mem_toFinset.mpr hz,rfl⟩
        · exact ⟨le_rfl,le_rfl⟩
      · refine mem_iUnion.mpr ⟨(mesh j.castSucc,mesh j.succ),mem_iUnion.mpr ⟨Finset.mem_union_left _ ?_,ht⟩⟩
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩
    · intro ht
      obtain ⟨lr,hlr⟩ := mem_iUnion.mp ht
      obtain ⟨hlr,ht⟩ := mem_iUnion.mp hlr
      rcases Finset.mem_union.mp hlr with hi | hp
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
        exact (hscalar t).mp (hnegative j (Finset.mem_filter.mp hj).2 t ht)
      · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hp
        have hts : t = s := le_antisymm ht.2 ht.1
        subst t
        exact (hscalar s).mp (hzeros.mem_toFinset.mp hs).le


private theorem embedded_disk_trace_finite_pieces
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (d : C(Metric.closedBall (0 : Plane) 1,↥F)) (hd : IsEmbedding d)
    (a : C(Interval,↥F)) (ha : IsEmbedding a)
    (hboundary : ((d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1}) ∩ range a).Finite) :
    ∃ pieces : Finset (Interval × Interval),
      (∀ lr ∈ pieces, lr.1 ≤ lr.2) ∧
      range d ∩ range a = ⋃ lr ∈ pieces, a '' Icc lr.1 lr.2 := by
  classical
  let D : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
  let f : C(Interval,S) := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
  have hD : IsEmbedding D := IsEmbedding.subtypeVal.comp hd
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp ha
  have hdfinite : ((D '' {z | z.val ∈ Metric.sphere (0 : Plane) 1}) ∩ range f).Finite := by
    apply (hboundary.image Subtype.val).subset
    rintro p ⟨⟨z,hz,rfl⟩,⟨t,ht⟩⟩
    refine ⟨d z,⟨⟨z,hz,rfl⟩,⟨t,Subtype.ext ht⟩⟩,rfl⟩
  let A := f ⁻¹' range D
  have hA : IsClosed A := (isCompact_range D.continuous).isClosed.preimage f.continuous
  have hfront : (frontier A).Finite := by
    have hb : (f ⁻¹' ((D '' {z | z.val ∈ Metric.sphere (0 : Plane) 1}) ∩ range f)).Finite :=
      hdfinite.preimage hf.injective.injOn
    apply hb.subset
    intro t ht
    exact ⟨CurveComplex.embedded_disk_frontier_subset_boundary D hD
      (f.continuous.frontier_preimage_subset (range D) ht),mem_range_self _⟩
  obtain ⟨pieces,horder,hpieces⟩ := closed_interval_set_finite_frontier_pieces A hA hfront
  refine ⟨pieces,horder,?_⟩
  ext y
  constructor
  · rintro ⟨⟨z,hz⟩,⟨t,ht⟩⟩
    have htA : t ∈ A := ⟨z,by exact congrArg Subtype.val (hz.trans ht.symm)⟩
    rw [hpieces] at htA
    obtain ⟨lr,htA⟩ := mem_iUnion.mp htA
    obtain ⟨hlr,htlr⟩ := mem_iUnion.mp htA
    exact mem_iUnion.mpr ⟨lr,mem_iUnion.mpr ⟨hlr,⟨t,htlr,ht⟩⟩⟩
  · intro hy
    obtain ⟨lr,hy⟩ := mem_iUnion.mp hy
    obtain ⟨hlr,t,ht,rfl⟩ := mem_iUnion.mp hy
    have htA : t ∈ A := hpieces.symm ▸ mem_iUnion.mpr ⟨lr,mem_iUnion.mpr ⟨hlr,ht⟩⟩
    obtain ⟨z,hz⟩ := htA
    exact ⟨⟨z,Subtype.ext hz⟩,mem_range_self _⟩


private theorem affine_parameter_range (s t : Interval) :
    range (CurveComplex.BranchedDoubleCover.intervalAffine s t) = uIcc s t := by
  open CurveComplex.BranchedDoubleCover in
    have hcont : Continuous (intervalAffine s t) := (intervalSegment s t).continuous
    have hs : s ∈ range (intervalAffine s t) := ⟨0,by simp [intervalAffine]⟩
    have ht : t ∈ range (intervalAffine s t) := ⟨1,by simp [intervalAffine]⟩
    apply Set.Subset.antisymm
    · rintro x ⟨q,rfl⟩
      rcases le_total s t with hst | hts
      · simpa [uIcc_of_le hst] using intervalAffine_mem_Icc hst q
      · have he : intervalAffine s t q = intervalAffine t s (unitInterval.symm q) := by
          apply Subtype.ext
          simp [intervalAffine,unitInterval.symm]
          ring
        rw [he,uIcc_of_ge hts]
        exact intervalAffine_mem_Icc hts _
    · exact (isPreconnected_range hcont).ordConnected.uIcc_subset hs ht

private theorem affine_subarc_range {X : Type*} [TopologicalSpace X]
    (a f : C(Interval,X)) (s t : Interval)
    (hf : ∀ q, f q = a (CurveComplex.BranchedDoubleCover.intervalAffine s t q)) :
    range f = a '' uIcc s t := by
  have he : (f : Interval → X) = a ∘ CurveComplex.BranchedDoubleCover.intervalAffine s t := funext hf
  rw [he,Set.range_comp,affine_parameter_range]



open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open scoped BigOperators
set_option maxHeartbeats 2200000
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- M0 (ordinary): finite old contacts and full continuous trace pieces, with the literal original contact partition. -/
theorem regional_paired_disk_finite_fan_carrier
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
        Nonempty (FiniteFanCarrier F
          (augmented (fun i => (r i).val.val) α.val.val) {some v,some w}
          (range d.first ∪ range d.second) V (range d.disk)
          (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v)) ∧
        (range d.first ∩ range α.val.val).Finite ∧
        (range d.second ∩ range α.val.val).Finite ∧
        (∀ j, j ≠ v → j ≠ w →
          (range (r v).val.val ∩ range (r j).val.val) =
            (((range d.first \ C₀) ∩ range (r j).val.val) ∪
              ((range (r v).val.val \ range d.first) ∩ range (r j).val.val)) ∪
              (C₀ ∩ range (r j).val.val) ∧
          Disjoint ((range d.first \ C₀) ∩ range (r j).val.val)
            ((range (r v).val.val \ range d.first) ∩ range (r j).val.val) ∧
          Disjoint ((range d.first \ C₀) ∩ range (r j).val.val)
            (C₀ ∩ range (r j).val.val) ∧
          Disjoint ((range (r v).val.val \ range d.first) ∩ range (r j).val.val)
            (C₀ ∩ range (r j).val.val) ∧
          ((range d.first \ C₀) ∩ range (r j).val.val).Finite ∧
          ((range d.second \ C₀) ∩ range (r j).val.val).Finite ∧
          ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).Finite ∧
          (C₀ ∩ range (r j).val.val).Finite ∧
          (range (r v).val.val ∩ range (r j).val.val).ncard = removed j + offset j) := by
  classical
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV hVinside havoid
    C₀ removed guiding offset
  have hfirst : range d.first ⊆ range (r v).val.val := by
    rintro y ⟨t,rfl⟩
    exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine d.aStart d.aFinish t,
      (d.first_eq t).symm⟩
  have hsecond : range d.second ⊆ range (r w).val.val := by
    rintro y ⟨t,rfl⟩
    exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish t,
      (d.second_eq t).symm⟩
  have hcorner : C₀ ⊆ range d.first := by
    intro y hy
    change y ∈ ({d.first 0,d.first 1} : Set ↥F) at hy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> exact Set.mem_range_self _
  have hfirstObserver : (range d.first ∩ range α.val.val).Finite := by
    exact (hinv.2.2.2.2 v).subset (fun y hy => ⟨hy.2,hfirst hy.1⟩)
  have hsecondObserver : (range d.second ∩ range α.val.val).Finite := by
    exact (hinv.2.2.2.2 w).subset (fun y hy => ⟨hy.2,hsecond hy.1⟩)
  have hpartition (A D K C : Set ↥F) (hKA : K ⊆ A) (hCK : C ⊆ K)
      (hf : (A ∩ D).Finite) :
      A ∩ D = (((K \ C) ∩ D) ∪ ((A \ K) ∩ D)) ∪ (C ∩ D) ∧
      Disjoint ((K \ C) ∩ D) ((A \ K) ∩ D) ∧
      Disjoint ((K \ C) ∩ D) (C ∩ D) ∧
      Disjoint ((A \ K) ∩ D) (C ∩ D) ∧
      ((K \ C) ∩ D).Finite ∧ ((A \ K) ∩ D).Finite ∧ (C ∩ D).Finite ∧
      (A ∩ D).ncard = ((K \ C) ∩ D).ncard +
        (((A \ K) ∩ D).ncard + (C ∩ D).ncard) := by
    have hKF : (K ∩ D).Finite := hf.subset (fun x hx => ⟨hKA hx.1,hx.2⟩)
    have hPF : ((K \ C) ∩ D).Finite := hKF.subset (fun x hx => ⟨hx.1.1,hx.2⟩)
    have hQF : ((A \ K) ∩ D).Finite := hf.subset (fun x hx => ⟨hx.1.1,hx.2⟩)
    have hCF : (C ∩ D).Finite := hKF.subset (fun x hx => ⟨hCK hx.1,hx.2⟩)
    have hsplit : A ∩ D = (((K \ C) ∩ D) ∪ ((A \ K) ∩ D)) ∪ (C ∩ D) := by
      ext x
      simp only [mem_inter_iff,mem_union,mem_sdiff]
      constructor
      · rintro ⟨ha,hd⟩
        by_cases hk : x ∈ K
        · by_cases hc : x ∈ C
          · exact Or.inr ⟨hc,hd⟩
          · exact Or.inl (Or.inl ⟨⟨hk,hc⟩,hd⟩)
        · exact Or.inl (Or.inr ⟨⟨ha,hk⟩,hd⟩)
      · rintro ((⟨⟨hk,hc⟩,hd⟩ | ⟨⟨ha,hk⟩,hd⟩) | ⟨hc,hd⟩)
        · exact ⟨hKA hk,hd⟩
        · exact ⟨ha,hd⟩
        · exact ⟨hKA (hCK hc),hd⟩
    have hPQ : Disjoint ((K \ C) ∩ D) ((A \ K) ∩ D) :=
      disjoint_left.mpr (fun x hx hy => hy.1.2 hx.1.1)
    have hPC : Disjoint ((K \ C) ∩ D) (C ∩ D) :=
      disjoint_left.mpr (fun x hx hy => hx.1.2 hy.1)
    have hQC : Disjoint ((A \ K) ∩ D) (C ∩ D) :=
      disjoint_left.mpr (fun x hx hy => hx.1.2 (hCK hy.1))
    refine ⟨hsplit,hPQ,hPC,hQC,hPF,hQF,hCF,?_⟩
    rw [hsplit,ncard_union_eq (hPC.union_left hQC) (hPF.union hQF) hCF,
      ncard_union_eq hPQ hPF hQF]
    omega
  let a : Option ι → C(Interval,↥F) := augmented (fun i => (r i).val.val) α.val.val
  let events := contactSites F a {some v,some w} (range d.first ∪ range d.second) V
  have haugFinite : ∀ i j : Option ι, i ≠ j → (range (a i) ∩ range (a j)).Finite := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hinv.2.2.2.2 j
    | some i =>
      cases j with
      | none => exact (hinv.2.2.2.2 i).subset (fun y hy => ⟨hy.2,hy.1⟩)
      | some j => exact hinv.1 i j (fun he => hij (congrArg some he))
  have heventsFinite : events.Finite := by
    have hfinite : (⋃ i : Option ι, ⋃ j : Option ι,
        if i = j then (∅ : Set ↥F) else range (a i) ∩ range (a j)).Finite := by
      apply Set.finite_iUnion
      intro i
      apply Set.finite_iUnion
      intro j
      split_ifs with he
      · exact Set.finite_empty
      · exact haugFinite i j he
    apply hfinite.subset
    intro p hp
    obtain ⟨hpV,hps,i,hi,j,hij,hpij⟩ := hp
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,by simpa [hij] using hpij⟩⟩
  have hforbidden : (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v).Finite := by
    apply ((Set.finite_range (fun j : ι => (r j).val.val 0)).union
      ((Set.finite_range (fun j : ι => (r j).val.val 1)).union
        (Set.toFinite ({α.val.val 0,α.val.val 1} : Set ↥F)))).subset
    rintro p (⟨j,hj,hp | hp⟩ | hp | hp)
    · exact Or.inl ⟨j,hp.symm⟩
    · exact Or.inr (Or.inl ⟨j,hp.symm⟩)
    · exact Or.inr (Or.inr (by simp [hp]))
    · exact Or.inr (Or.inr (by simp [hp]))
  have hsides : range d.first ∪ range d.second ⊆ range d.disk := by
    rw [←d.boundary_image]
    exact Set.image_subset_range _ _
  have heventsInterior : ∀ p ∈ events, p.val ∈ interior F := by
    intro p hp
    exact d.ambient_interior p (hsides hp.2.1)
  have hBF : boundaryCircle ⊆ frontier F := by
    dsimp only [boundaryCircle]
    rw [hfrontier]
    exact Set.subset_union_left
  have haugProper : ∀ i : Option ι,
      IsEmbedding (a i) ∧ (a i 0).val ∈ frontier F ∧ (a i 1).val ∈ frontier F := by
    intro i
    cases i with
    | none => exact ⟨α.val.property.1,hBF α.val.property.2.1,hBF α.val.property.2.2.1⟩
    | some i => exact ⟨(r i).val.property.1,hBF (r i).val.property.2.1,
        hBF (r i).val.property.2.2.1⟩
  have heventParameter : ∀ p ∈ events, ∀ i (t : Interval), a i t = p → t ∈ Ioo (0 : Interval) 1 := by
    intro p hp i t ht
    have hpi := heventsInterior p hp
    have hpOff : p.val ∉ frontier F := by
      exact fun h => h.2 hpi
    have ht0 : t ≠ 0 := by
      intro he
      exact hpOff (ht ▸ (he ▸ (haugProper i).2.1))
    have ht1 : t ≠ 1 := by
      intro he
      exact hpOff (ht ▸ (he ▸ (haugProper i).2.2))
    exact ⟨lt_of_le_of_ne bot_le (Ne.symm ht0),lt_of_le_of_ne le_top ht1⟩
  have heventCrossing : ∀ p ∈ events, ∀ i j, i ≠ j →
      ∀ u t : Interval, a i u = p → a j t = p →
      ∃ C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F (a i) (a j) u t,
        C.OppositeSides := by
    intro p hp i j hij u t hu ht
    exact hcross i j hij u t (heventParameter p hp i u hu)
      (heventParameter p hp j t ht) (hu.trans ht.symm)
  -- Continuous pieces for the actual disk; contacts remain finite events.
  have hpieces : ∃ pieces : Option ι → Finset (Interval × Interval),
      (∀ i, ∀ lr ∈ pieces i, lr.1 ≤ lr.2) ∧
      (∀ i, range d.disk ∩ range (a i) = ⋃ lr ∈ pieces i, a i '' Icc lr.1 lr.2) := by
    let : ClosedSurface S := Classical.choice hS.2.1
    have hpieceOne (i : Option ι) : ∃ pieces : Finset (Interval × Interval),
        (∀ lr ∈ pieces, lr.1 ≤ lr.2) ∧
        range d.disk ∩ range (a i) = ⋃ lr ∈ pieces, a i '' Icc lr.1 lr.2 := by
      by_cases hiv : i = some v
      · subst i
        refine ⟨{(min d.aStart d.aFinish,max d.aStart d.aFinish)},?_,?_⟩
        · intro lr hlr
          rw [Finset.mem_singleton] at hlr
          subst lr
          exact min_le_max
        · have he := d.whole_first.trans
            (affine_subarc_range (r v).val.val d.first d.aStart d.aFinish d.first_eq)
          simpa only [a,augmented,Option.elim_some,Finset.mem_singleton,
            Set.iUnion_iUnion_eq_left,Set.uIcc] using he
      by_cases hiw : i = some w
      · subst i
        refine ⟨{(min d.bStart d.bFinish,max d.bStart d.bFinish)},?_,?_⟩
        · intro lr hlr
          rw [Finset.mem_singleton] at hlr
          subst lr
          exact min_le_max
        · have he := d.whole_second.trans
            (affine_subarc_range (r w).val.val d.second d.bStart d.bFinish d.second_eq)
          simpa only [a,augmented,Option.elim_some,Finset.mem_singleton,
            Set.iUnion_iUnion_eq_left,Set.uIcc] using he
      have hf : (range d.first ∩ range (a i)).Finite :=
        (haugFinite (some v) i (Ne.symm hiv)).subset (fun y hy => ⟨hfirst hy.1,hy.2⟩)
      have hg : (range d.second ∩ range (a i)).Finite :=
        (haugFinite (some w) i (Ne.symm hiw)).subset (fun y hy => ⟨hsecond hy.1,hy.2⟩)
      apply embedded_disk_trace_finite_pieces F d.disk d.disk_embedded (a i) (haugProper i).1
      rw [d.boundary_image,union_inter_distrib_right]
      exact hf.union hg
    choose pieces horder hwhole using hpieceOne
    exact ⟨pieces,horder,hwhole⟩
  -- Consume the reviewed, proved whole-trace window geometry for this exact family and disk.
  have hfans : ∃ window : ∀ p : ↥events, IncidentFanWindow F a V p.val,
      (∀ p q : ↥events, p ≠ q →
        Disjoint (RegionalChordNormalization.chartPull F (window p).chart (Metric.closedBall (0 : Plane) 1))
          (RegionalChordNormalization.chartPull F (window q).chart (Metric.closedBall (0 : Plane) 1))) ∧
      (∀ p : ↥events, ∀ i, i ∈ ({some v,some w} : Set (Option ι)) →
        ∀ hip : p.val ∈ range (a i),
        ∃ A : IncidentFanWindow F a V p.val,
          RegionalChordNormalization.chartPull F A.chart (Metric.closedBall (0 : Plane) 1) ⊆
            RegionalChordNormalization.chartPull F (window p).chart (Metric.ball (0 : Plane) 1) ∧
          incidentPorts a p.val A.chart A.left A.right (⟨i,hip⟩,false) 1 = 0 ∧
          incidentPorts a p.val A.chart A.left A.right (⟨i,hip⟩,true) 1 = 0 ∧
          ∀ j : incidentIndex a p.val, j.val ≠ i →
            ((0 < incidentPorts a p.val A.chart A.left A.right (j,false) 1 ∧
              incidentPorts a p.val A.chart A.left A.right (j,true) 1 < 0) ∨
            (incidentPorts a p.val A.chart A.left A.right (j,false) 1 < 0 ∧
              0 < incidentPorts a p.val A.chart A.left A.right (j,true) 1))) ∧
      (∀ p : ↥events, ∀ i j, i ≠ j →
        (i ∈ ({some v,some w} : Set (Option ι)) ∨ j ∈ ({some v,some w} : Set (Option ι))) →
        ∀ u t : Interval, u ∈ Ioo (0 : Interval) 1 → t ∈ Ioo (0 : Interval) 1 →
        a i u = p.val → a j t = p.val →
        ∃ C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F (a i) (a j) u t,
          C.OppositeSides ∧
          {y : ↥F | y.val ∈ C.chart.source ∧ C.chart y.val ∈ Plane.closedSquare 0 1} ⊆ V) := by
    exact regional_paired_disk_fan_window_geometry S g hg hS x R hR htarget
      F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
      ι r α hinv hcross v w hvw d V hV hdV hVinside havoid
  obtain ⟨pieces,horder,hwhole⟩ := hpieces
  obtain ⟨window,hdisjointWindows,haxes,hopp⟩ := hfans
  have hcarrier : Nonempty (FiniteFanCarrier F a {some v,some w}
      (range d.first ∪ range d.second) V (range d.disk)
      (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v)) := by
    exact ⟨{
      events := events
      events_finite := heventsFinite
      events_exact := rfl
      pieces := pieces
      piece_order := horder
      whole_trace_pieces := hwhole
      carrier_in_V := hdV
      forbidden_finite := hforbidden
      window := window
      windows_disjoint := hdisjointWindows
      selected_axis_fans := haxes
      opposite_side_charts := hopp }⟩
  refine ⟨hcarrier,hfirstObserver,hsecondObserver,?_⟩
  intro j hjv hjw
  obtain ⟨hpart,hPQ,hPC,hQC,hPF,hQF,hCF,hcard⟩ :=
    hpartition (range (r v).val.val) (range (r j).val.val) (range d.first) C₀
      hfirst hcorner (hinv.1 v j (Ne.symm hjv))
  exact ⟨hpart,hPQ,hPC,hQC,hPF,
    (hinv.1 w j (Ne.symm hjw)).subset (fun y hy => ⟨hsecond hy.1.1,hy.2⟩),
    hQF,hCF,hcard⟩
