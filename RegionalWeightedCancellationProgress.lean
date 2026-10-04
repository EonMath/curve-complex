import CurveComplexGenusTwo.Topology.ActualRegionalBoundaryTracks.RegionalDecreaseSupport
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalBoundaryParallelTransport
import RegionalHalfMovieScaffold

open CurveComplex Set Topology RegionalTotalDecrease
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- PLAN D: conditional weighted half cancellation, with actual F movie and every third-count/corner offset. -/
theorem regional_weighted_paired_half_bigon_replacement
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
      ∀ d : PairedHalfBigonDisk F {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F} (r v).val.val (r w).val.val,
      ∀ V : Set ↥F, IsOpen V → range d.disk ⊆ V →
        Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ boundaryCircle}) →
        let C₀ : Set ↥F := {d.first 1}
        let removed := fun j : ι => ((range d.first \ C₀) ∩ range (r j).val.val).ncard
        let guiding := fun j : ι => ((range d.second \ C₀) ∩ range (r j).val.val).ncard
        let offset := fun j : ι =>
          ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard +
            (C₀ ∩ range (r j).val.val).ncard
        (∑ j : ι, if j ≠ v ∧ j ≠ w then guiding j else 0) ≤
          (∑ j : ι, if j ≠ v ∧ j ≠ w then removed j else 0) →
        ∃ (q : IntrinsicEssentialArc) (H : AmbientIsotopy ↥F),
          ClassMovie {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F}
            (r v).val.val q.val.val H ∧
          (∀ t y, y ∉ V → H.map (t,y) = y) ∧
          Quot.mk intrinsicArcRel q = Quot.mk intrinsicArcRel (r v) ∧
          FamilyInvariant (fun j => (Function.update r v q j).val.val) α.val.val ∧
          (∀ j, j ≠ v → (range q.val.val ∩ range (r j).val.val).Finite) ∧
          (range q.val.val ∩ range α.val.val).Finite ∧
          (∀ j, j ≠ v → j ≠ w →
            ((range d.first \ C₀) ∩ range (r j).val.val).Finite ∧
            ((range d.second \ C₀) ∩ range (r j).val.val).Finite ∧
            ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).Finite ∧
            (C₀ ∩ range (r j).val.val).Finite ∧
            (range (r v).val.val ∩ range (r j).val.val).ncard = removed j + offset j ∧
            (range q.val.val ∩ range (r j).val.val).ncard ≤ guiding j + offset j) ∧
          (range q.val.val ∩ range (r w).val.val).ncard + 1 ≤
            (range (r v).val.val ∩ range (r w).val.val).ncard ∧
          (∑ j : ι, if v = j then 0 else
            (range q.val.val ∩ range (r j).val.val).ncard) <
            (∑ j : ι, if v = j then 0 else
              (range (r v).val.val ∩ range (r j).val.val).ncard) := by
  classical
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV havoid
    C₀ removed guiding offset hcheap
  have hBF : boundaryCircle ⊆ frontier F := by
    dsimp only [boundaryCircle]
    rw [hfrontier]
    exact Set.subset_union_left
  have hfirst : range d.first ⊆ range (r v).val.val := by
    rintro y ⟨t,rfl⟩
    exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine d.aStart d.aFinish t,(d.first_eq t).symm⟩
  have hsecond : range d.second ⊆ range (r w).val.val := by
    rintro y ⟨t,rfl⟩
    exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish t,(d.second_eq t).symm⟩
  have hcorner : C₀ ⊆ range d.first := by
    intro y hy
    change y ∈ ({d.first 1} : Set ↥F) at hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact Set.mem_range_self _
  have hpartition (A D K C : Set ↥F) (hKA : K ⊆ A) (hCK : C ⊆ K)
      (hf : (A ∩ D).Finite) :
      ((K \ C) ∩ D).Finite ∧ ((A \ K) ∩ D).Finite ∧ (C ∩ D).Finite ∧
      (A ∩ D).ncard = ((K \ C) ∩ D).ncard +
        (((A \ K) ∩ D).ncard + (C ∩ D).ncard) := by
    have hKF : (K ∩ D).Finite := hf.subset (fun x hx => ⟨hKA hx.1,hx.2⟩)
    have hPF : ((K \ C) ∩ D).Finite := hKF.subset (fun x hx => ⟨hx.1.1,hx.2⟩)
    have hQF : ((A \ K) ∩ D).Finite := hf.subset (fun x hx => ⟨hx.1.1,hx.2⟩)
    have hCF : (C ∩ D).Finite := hKF.subset (fun x hx => ⟨hCK hx.1,hx.2⟩)
    have hsplitA : A ∩ D = (K ∩ D) ∪ ((A \ K) ∩ D) := by
      ext x
      simp only [mem_inter_iff,mem_union,mem_diff]
      constructor
      · rintro ⟨ha,hd⟩
        by_cases hk : x ∈ K
        · exact Or.inl ⟨hk,hd⟩
        · exact Or.inr ⟨⟨ha,hk⟩,hd⟩
      · rintro (⟨hk,hd⟩ | ⟨⟨ha,hk⟩,hd⟩)
        · exact ⟨hKA hk,hd⟩
        · exact ⟨ha,hd⟩
    have hsplitK : K ∩ D = ((K \ C) ∩ D) ∪ (C ∩ D) := by
      ext x
      simp only [mem_inter_iff,mem_union,mem_diff]
      constructor
      · rintro ⟨hk,hd⟩
        by_cases hc : x ∈ C
        · exact Or.inr ⟨hc,hd⟩
        · exact Or.inl ⟨⟨hk,hc⟩,hd⟩
      · rintro (⟨⟨hk,hc⟩,hd⟩ | ⟨hc,hd⟩)
        · exact ⟨hk,hd⟩
        · exact ⟨hCK hc,hd⟩
    have hdA : Disjoint (K ∩ D) ((A \ K) ∩ D) :=
      disjoint_left.mpr (fun x hx hy => hy.1.2 hx.1)
    have hdK : Disjoint ((K \ C) ∩ D) (C ∩ D) :=
      disjoint_left.mpr (fun x hx hy => hx.1.2 hy.1)
    have hcardA : (A ∩ D).ncard = (K ∩ D).ncard + ((A \ K) ∩ D).ncard := by
      rw [hsplitA]
      exact ncard_union_eq hdA hKF hQF
    have hcardK : (K ∩ D).ncard = ((K \ C) ∩ D).ncard + (C ∩ D).ncard := by
      rw [hsplitK]
      exact ncard_union_eq hdK hPF hCF
    refine ⟨hPF,hQF,hCF,?_⟩
    omega
  have hcountdata (j : ι) (hjv : j ≠ v) (hjw : j ≠ w) :
      ((range d.first \ C₀) ∩ range (r j).val.val).Finite ∧
      ((range d.second \ C₀) ∩ range (r j).val.val).Finite ∧
      ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).Finite ∧
      (C₀ ∩ range (r j).val.val).Finite ∧
      (range (r v).val.val ∩ range (r j).val.val).ncard = removed j + offset j := by
    obtain ⟨hr,he,hc,hcard⟩ := hpartition (range (r v).val.val)
      (range (r j).val.val) (range d.first) C₀ hfirst hcorner
      (hinv.1 v j (Ne.symm hjv))
    refine ⟨hr,?_,he,hc,hcard⟩
    exact (hinv.1 w j (Ne.symm hjw)).subset
      (fun y hy => ⟨hsecond hy.1.1,hy.2⟩)
  have hrow (δ : ℕ) (hδ : 0 < δ) (old new f g o : ι → ℕ)
      (hpair : new w + δ ≤ old w)
      (hold : ∀ j, j ≠ v → j ≠ w → old j = f j + o j)
      (hnew : ∀ j, j ≠ v → j ≠ w → new j ≤ g j + o j)
      (hcheap : (∑ j, if j ≠ v ∧ j ≠ w then g j else 0) ≤
        ∑ j, if j ≠ v ∧ j ≠ w then f j else 0) :
      (∑ j, if v = j then 0 else new j) <
        ∑ j, if v = j then 0 else old j := by
    have hsplit (f : ι → ℕ) :
        (∑ j, if v = j then 0 else f j) =
          f w + ∑ j, if j ≠ v ∧ j ≠ w then f j else 0 := by
      have he (j : ι) : (if v = j then 0 else f j) =
          (if j = w then f w else 0) +
            (if j ≠ v ∧ j ≠ w then f j else 0) := by
        by_cases hjv : j = v
        · subst j
          simp [hvw]
        · by_cases hjw : j = w
          · subst j
            simp [hvw,Ne.symm hvw]
          · simp [hjv,hjw,Ne.symm hjv]
      simp_rw [he,Finset.sum_add_distrib]
      simp
    have hOld : (∑ j, if j ≠ v ∧ j ≠ w then old j else 0) =
        (∑ j, if j ≠ v ∧ j ≠ w then f j else 0) +
          ∑ j, if j ≠ v ∧ j ≠ w then o j else 0 := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs with h
      · exact hold j h.1 h.2
      · simp
    have hNew : (∑ j, if j ≠ v ∧ j ≠ w then new j else 0) ≤
        (∑ j, if j ≠ v ∧ j ≠ w then g j else 0) +
          ∑ j, if j ≠ v ∧ j ≠ w then o j else 0 := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with h
      · exact hnew j h.1 h.2
      · simp
    rw [hsplit old,hsplit new,hOld]
    omega
  -- Atomic outstanding producer: a boundary-moving F movie, including endpoint
  -- avoidance and every third-trace bound; the B side is not appended to q.
  have hgeometry : ∃ H : AmbientIsotopy ↥F,
      (∀ t y, y ∉ V → H.map (t,y) = y) ∧
      (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ boundaryCircle} =
        {y : ↥F | y.val ∈ boundaryCircle}) ∧
      (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
        {y : ↥F | y.val ∈ frontier F}) ∧
      (∀ j, j ≠ v →
        H.finalMap ((r v).val.val 0) ≠ (r j).val.val 0 ∧
        H.finalMap ((r v).val.val 0) ≠ (r j).val.val 1 ∧
        H.finalMap ((r v).val.val 1) ≠ (r j).val.val 0 ∧
        H.finalMap ((r v).val.val 1) ≠ (r j).val.val 1) ∧
      α.val.val 0 ∉ H.finalMap '' range (r v).val.val ∧
      α.val.val 1 ∉ H.finalMap '' range (r v).val.val ∧
      (∀ j, j ≠ v →
        (H.finalMap '' range (r v).val.val ∩ range (r j).val.val).Finite) ∧
      (H.finalMap '' range (r v).val.val ∩ range α.val.val).Finite ∧
      (∀ j, j ≠ v → j ≠ w →
        (H.finalMap '' range (r v).val.val ∩ range (r j).val.val).ncard ≤
          guiding j + offset j) ∧
      (H.finalMap '' range (r v).val.val ∩ range (r w).val.val).ncard + 1 ≤
        (range (r v).val.val ∩ range (r w).val.val).ncard := by
    exact regional_half_disk_supported_movie_geometry S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier ι r α hinv hcross v w hvw d V hV hdV havoid hcheap
  obtain ⟨H,hout,hB,hT,hendsRaw,ha0Raw,ha1Raw,hfinite,halphafinite,hbound,hpair⟩ :=
    hgeometry
  obtain ⟨h,hh⟩ := H.homeomorphism_at 1
  let amap : C(Interval,↥F) :=
    ⟨fun t => h ((r v).val.val t),h.continuous.comp (r v).val.val.continuous⟩
  have hmove : H.finalMap '' range (r v).val.val = range amap := by
    rw [←Set.range_comp]
    apply congrArg Set.range
    funext t
    exact (hh ((r v).val.val t)).symm
  have hamb : Topology.IsEmbedding amap :=
    h.isEmbedding.comp (r v).val.property.1
  have hBmem (y : ↥F) (hy : y.val ∈ boundaryCircle) :
      (h y).val ∈ boundaryCircle := by
    have hy' : h y ∈ (fun y => H.map (1,y)) ''
        {y : ↥F | y.val ∈ boundaryCircle} := ⟨y,hy,(hh y).symm⟩
    change h y ∈ {y : ↥F | y.val ∈ boundaryCircle}
    rw [←hB 1]
    exact hy'
  have hTmem (y : ↥F) : (h y).val ∈ frontier F ↔ y.val ∈ frontier F := by
    constructor
    · intro hy
      have hy' : h y ∈ (fun y => H.map (1,y)) ''
          {y : ↥F | y.val ∈ frontier F} := (hT 1).symm ▸ hy
      obtain ⟨z,hz,hzy⟩ := hy'
      have he : z = y := h.injective ((hh z).trans hzy)
      exact he ▸ hz
    · intro hy
      have hy' : h y ∈ (fun y => H.map (1,y)) ''
          {y : ↥F | y.val ∈ frontier F} := ⟨y,hy,(hh y).symm⟩
      change h y ∈ {y : ↥F | y.val ∈ frontier F}
      rw [←hT 1]
      exact hy'
  have haI : ∀ t ∈ Set.Ioo (0 : Interval) 1, (amap t).val ∉ frontier F := by
    intro t ht hmem
    exact (r v).val.property.2.2.2 t ht ((hTmem _).mp hmem)
  let qp : RegionProperArc :=
    ⟨amap,hamb,hBmem _ (r v).val.property.2.1,
      hBmem _ (r v).val.property.2.2.1,haI⟩
  have hess : ¬ regionBoundaryParallel qp :=
    (regional_essential_arc_ambient_transport F boundaryCircle
      (r v).val.val amap H (hB 1) hmove).mp (r v).property
  let q : IntrinsicEssentialArc := ⟨qp,hess⟩
  have hqimage : H.finalMap '' range (r v).val.val = range q.val.val := hmove
  have hmovie : ClassMovie {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F}
      (r v).val.val q.val.val H := ⟨hB,hT,hqimage⟩
  have hclass : Quot.mk intrinsicArcRel q = Quot.mk intrinsicArcRel (r v) := by
    symm
    exact Quot.sound ⟨H,hB,hT,hqimage⟩
  have hqfinite (j : ι) (hj : j ≠ v) :
      (range q.val.val ∩ range (r j).val.val).Finite := by
    rw [←hqimage]
    exact hfinite j hj
  have hqalpha : (range q.val.val ∩ range α.val.val).Finite := by
    rw [←hqimage]
    exact halphafinite
  have hends (j : ι) (hj : j ≠ v) :
      q.val.val 0 ≠ (r j).val.val 0 ∧ q.val.val 0 ≠ (r j).val.val 1 ∧
      q.val.val 1 ≠ (r j).val.val 0 ∧ q.val.val 1 ≠ (r j).val.val 1 := by
    change h ((r v).val.val 0) ≠ _ ∧ h ((r v).val.val 0) ≠ _ ∧
      h ((r v).val.val 1) ≠ _ ∧ h ((r v).val.val 1) ≠ _
    rw [hh,hh]
    change H.finalMap ((r v).val.val 0) ≠ _ ∧ H.finalMap ((r v).val.val 0) ≠ _ ∧
      H.finalMap ((r v).val.val 1) ≠ _ ∧ H.finalMap ((r v).val.val 1) ≠ _
    exact hendsRaw j hj
  have ha0 : α.val.val 0 ∉ range q.val.val := hqimage ▸ ha0Raw
  have ha1 : α.val.val 1 ∉ range q.val.val := hqimage ▸ ha1Raw
  have hinvNew : FamilyInvariant
      (fun j => (Function.update r v q j).val.val) α.val.val := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i j hij
      by_cases hi : i = v
      · subst i
        have hj : j ≠ v := Ne.symm hij
        simpa [Function.update,hj] using hqfinite j hj
      · by_cases hj : j = v
        · subst j
          simpa [Function.update,hi,Set.inter_comm] using hqfinite i hi
        · simpa [Function.update,hi,hj] using hinv.1 i j hij
    · intro i j hij
      by_cases hi : i = v
      · subst i
        have hj : j ≠ v := Ne.symm hij
        simpa [Function.update,hj] using hends j hj
      · by_cases hj : j = v
        · subst j
          obtain ⟨h00,h01,h10,h11⟩ := hends i hi
          simpa [Function.update,hi] using
            And.intro h00.symm (And.intro h10.symm (And.intro h01.symm h11.symm))
        · simpa [Function.update,hi,hj] using hinv.2.1 i j hij
    · intro i
      by_cases hi : i = v
      · subst i
        simpa [Function.update] using ha0
      · simpa [Function.update,hi] using hinv.2.2.1 i
    · intro i
      by_cases hi : i = v
      · subst i
        simpa [Function.update] using ha1
      · simpa [Function.update,hi] using hinv.2.2.2.1 i
    · intro i
      by_cases hi : i = v
      · subst i
        simpa [Function.update,Set.inter_comm] using hqalpha
      · simpa [Function.update,hi] using hinv.2.2.2.2 i
  have hqbound (j : ι) (hjv : j ≠ v) (hjw : j ≠ w) :
      (range q.val.val ∩ range (r j).val.val).ncard ≤ guiding j + offset j := by
    rw [←hqimage]
    exact hbound j hjv hjw
  have hqpair : (range q.val.val ∩ range (r w).val.val).ncard + 1 ≤
      (range (r v).val.val ∩ range (r w).val.val).ncard := by
    rw [←hqimage]
    exact hpair
  have hqrow : (∑ j : ι, if v = j then 0 else
        (range q.val.val ∩ range (r j).val.val).ncard) <
      ∑ j : ι, if v = j then 0 else
        (range (r v).val.val ∩ range (r j).val.val).ncard :=
    hrow 1 (by norm_num)
      (fun j => (range (r v).val.val ∩ range (r j).val.val).ncard)
      (fun j => (range q.val.val ∩ range (r j).val.val).ncard)
      removed guiding offset hqpair
      (fun j hjv hjw => (hcountdata j hjv hjw).2.2.2.2) hqbound hcheap
  refine ⟨q,H,hmovie,hout,hclass, hinvNew,hqfinite,hqalpha,?_,hqpair,hqrow⟩
  intro j hjv hjw
  obtain ⟨hr,hg,he,hc,hcard⟩ := hcountdata j hjv hjw
  exact ⟨hr,hg,he,hc,hcard,hqbound j hjv hjw⟩
