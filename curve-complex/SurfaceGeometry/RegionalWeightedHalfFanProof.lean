import RegionalWeightedMovieDefinitions
import RegionalHalfFanWindowProof

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- M0 (half): finite old contacts and full continuous trace pieces, with the literal original contact partition. -/
theorem regional_paired_half_disk_finite_fan_carrier
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
  letI : ClosedSurface S := Classical.choice hS.2.1
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV havoid
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
    change y ∈ ({d.first 1} : Set ↥F) at hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact Set.mem_range_self _
  have hpartition (A D K C : Set ↥F) (hKA : K ⊆ A) (hCK : C ⊆ K)
      (hf : (A ∩ D).Finite) :
      A ∩ D = (((K \ C) ∩ D) ∪ ((A \ K) ∩ D)) ∪ (C ∩ D) ∧
      Disjoint ((K \ C) ∩ D) ((A \ K) ∩ D) ∧
      Disjoint ((K \ C) ∩ D) (C ∩ D) ∧
      Disjoint ((A \ K) ∩ D) (C ∩ D) ∧
      ((K \ C) ∩ D).Finite ∧ ((A \ K) ∩ D).Finite ∧ (C ∩ D).Finite ∧
      (A ∩ D).ncard = ((K \ C) ∩ D).ncard +
        (((A \ K) ∩ D).ncard + (C ∩ D).ncard) := by
    have hPF : ((K \ C) ∩ D).Finite := hf.subset
      (fun x hx => ⟨hKA hx.1.1,hx.2⟩)
    have hQF : ((A \ K) ∩ D).Finite := hf.subset
      (fun x hx => ⟨hx.1.1,hx.2⟩)
    have hCF : (C ∩ D).Finite := hf.subset
      (fun x hx => ⟨hKA (hCK hx.1),hx.2⟩)
    have hsplit : A ∩ D = (((K \ C) ∩ D) ∪ ((A \ K) ∩ D)) ∪ (C ∩ D) := by
      ext x
      simp only [mem_inter_iff,mem_union,mem_sdiff]
      constructor
      · rintro ⟨ha,hd⟩
        by_cases hc : x ∈ C
        · exact Or.inr ⟨hc,hd⟩
        · by_cases hk : x ∈ K
          · exact Or.inl (Or.inl ⟨⟨hk,hc⟩,hd⟩)
          · exact Or.inl (Or.inr ⟨⟨ha,hk⟩,hd⟩)
      · rintro ((⟨⟨hk,hc⟩,hd⟩ | ⟨⟨ha,hk⟩,hd⟩) | ⟨hc,hd⟩)
        · exact ⟨hKA hk,hd⟩
        · exact ⟨ha,hd⟩
        · exact ⟨hKA (hCK hc),hd⟩
    have hdPQ : Disjoint ((K \ C) ∩ D) ((A \ K) ∩ D) :=
      disjoint_left.mpr (fun x hx hy => hy.1.2 hx.1.1)
    have hdPC : Disjoint ((K \ C) ∩ D) (C ∩ D) :=
      disjoint_left.mpr (fun x hx hy => hx.1.2 hy.1)
    have hdQC : Disjoint ((A \ K) ∩ D) (C ∩ D) :=
      disjoint_left.mpr (fun x hx hy => hx.1.2 (hCK hy.1))
    refine ⟨hsplit,hdPQ,hdPC,hdQC,hPF,hQF,hCF,?_⟩
    rw [hsplit,ncard_union_eq (hdPC.union_left hdQC) (hPF.union hQF) hCF,
      ncard_union_eq hdPQ hPF hQF]
    omega
  have hαfirst : (range d.first ∩ range α.val.val).Finite :=
    (hinv.2.2.2.2 v).subset (fun y hy => ⟨hy.2,hfirst hy.1⟩)
  have hαsecond : (range d.second ∩ range α.val.val).Finite :=
    (hinv.2.2.2.2 w).subset (fun y hy => ⟨hy.2,hsecond hy.1⟩)
  let a : Option ι → C(Interval,↥F) :=
    augmented (fun i => (r i).val.val) α.val.val
  have hfinite (i j : Option ι) (hij : i ≠ j) :
      (range (a i) ∩ range (a j)).Finite := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hinv.2.2.2.2 j
    | some i =>
      cases j with
      | none => exact (hinv.2.2.2.2 i).subset (fun p hp => ⟨hp.2,hp.1⟩)
      | some j => exact hinv.1 i j (fun h => hij (congrArg some h))
  have hBFront : boundaryCircle ⊆ frontier F := by
    dsimp only [boundaryCircle]
    rw [hfrontier]
    exact Set.subset_union_left
  have hproper (i : Option ι) : Topology.IsEmbedding (a i) ∧
      ((a i) 0).val ∈ boundaryCircle ∧ ((a i) 1).val ∈ boundaryCircle ∧
      ∀ t ∈ Ioo (0 : Interval) 1, ((a i) t).val ∉ frontier F := by
    cases i with
    | none => exact α.val.property
    | some i => exact (r i).val.property
  have hends (i j : Option ι) (hij : i ≠ j) :
      a i 0 ≠ a j 0 ∧ a i 0 ≠ a j 1 ∧
      a i 1 ≠ a j 0 ∧ a i 1 ≠ a j 1 := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        exact ⟨(fun h => hinv.2.2.1 j ⟨0,h.symm⟩),
          (fun h => hinv.2.2.1 j ⟨1,h.symm⟩),
          (fun h => hinv.2.2.2.1 j ⟨0,h.symm⟩),
          (fun h => hinv.2.2.2.1 j ⟨1,h.symm⟩)⟩
    | some i =>
      cases j with
      | none =>
        exact ⟨(fun h => hinv.2.2.1 i ⟨0,h⟩),
          (fun h => hinv.2.2.2.1 i ⟨0,h⟩),
          (fun h => hinv.2.2.1 i ⟨1,h⟩),
          (fun h => hinv.2.2.2.1 i ⟨1,h⟩)⟩
      | some j => exact hinv.2.1 i j (fun h => hij (congrArg some h))
  have hend_clear (i j : Option ι) (hij : i ≠ j) :
      a i 0 ∉ range (a j) ∧ a i 1 ∉ range (a j) := by
    have hc (t : Interval) (ht : ((a j) t).val ∈ frontier F) : t = 0 ∨ t = 1 := by
      by_cases ht0 : t = 0
      · exact Or.inl ht0
      · by_cases ht1 : t = 1
        · exact Or.inr ht1
        · exact False.elim ((hproper j).2.2.2 t
            ⟨lt_of_le_of_ne bot_le (Ne.symm ht0),lt_of_le_of_ne le_top ht1⟩ ht)
    constructor
    · rintro ⟨t,ht⟩
      have hb : ((a j) t).val ∈ frontier F := by
        rw [ht]
        exact hBFront (hproper i).2.1
      obtain h0 | h1 := hc t hb
      · exact (hends i j hij).1 (by rw [← ht,h0])
      · exact (hends i j hij).2.1 (by rw [← ht,h1])
    · rintro ⟨t,ht⟩
      have hb : ((a j) t).val ∈ frontier F := by
        rw [ht]
        exact hBFront (hproper i).2.2.1
      obtain h0 | h1 := hc t hb
      · exact (hends i j hij).2.2.1 (by rw [← ht,h0])
      · exact (hends i j hij).2.2.2 (by rw [← ht,h1])
  have hcontact_params (i j : Option ι) (hij : i ≠ j)
      (u t : Interval) (hut : a i u = a j t) :
      u ∈ Ioo (0 : Interval) 1 ∧ t ∈ Ioo (0 : Interval) 1 := by
    have hu0 : u ≠ 0 := fun h => (hend_clear i j hij).1 ⟨t,hut.symm.trans (congrArg (a i) h)⟩
    have hu1 : u ≠ 1 := fun h => (hend_clear i j hij).2 ⟨t,hut.symm.trans (congrArg (a i) h)⟩
    have ht0 : t ≠ 0 := fun h => (hend_clear j i hij.symm).1 ⟨u,hut.trans (congrArg (a j) h)⟩
    have ht1 : t ≠ 1 := fun h => (hend_clear j i hij.symm).2 ⟨u,hut.trans (congrArg (a j) h)⟩
    exact ⟨⟨lt_of_le_of_ne bot_le hu0.symm,lt_of_le_of_ne le_top hu1⟩,
      ⟨lt_of_le_of_ne bot_le (Ne.symm ht0),lt_of_le_of_ne le_top ht1⟩⟩
  have hcontact_interior (i j : Option ι) (hij : i ≠ j)
      (p : ↥F) (hip : p ∈ range (a i)) (hjp : p ∈ range (a j)) :
      p.val ∈ interior F := by
    obtain ⟨u,hu⟩ := hip
    obtain ⟨t,ht⟩ := hjp
    have hparams := hcontact_params i j hij u t (hu.trans ht.symm)
    apply (mem_interior_iff_notMem_frontier p.property).mpr
    rw [← hu]
    exact (hproper i).2.2.2 u hparams.1
  have hevents : (contactSites F a {some v,some w}
      (range d.first ∪ range d.second) V).Finite := by
    let allContacts : Set ↥F := ⋃ i : Option ι, ⋃ j : Option ι,
      if i = j then ∅ else range (a i) ∩ range (a j)
    have hall : allContacts.Finite := by
      apply Set.finite_iUnion
      intro i
      apply Set.finite_iUnion
      intro j
      split
      · exact Set.finite_empty
      · exact hfinite i j ‹i ≠ j›
    apply hall.subset
    intro p hp
    obtain ⟨hpV,hps,i,hi,j,hij,hpij⟩ := hp
    exact Set.mem_iUnion₂.mpr ⟨i,j,by simpa only [if_neg hij] using hpij⟩
  have hforbidden : (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v).Finite := by
    have hf : (⋃ j : ι, ({(r j).val.val 0,(r j).val.val 1} : Set ↥F)).Finite :=
      Set.finite_iUnion (fun j => Set.toFinite _)
    apply (hf.union (Set.toFinite ({α.val.val 0,α.val.val 1} : Set ↥F))).subset
    intro p hp
    obtain (⟨j,hj,hp⟩ | hp | hp) := hp
    · exact Or.inl (Set.mem_iUnion.mpr ⟨j,by simpa only [Set.mem_insert_iff,
        Set.mem_singleton_iff] using hp⟩)
    · exact Or.inr (by simp [hp])
    · exact Or.inr (by simp [hp])
  have hfinite_interval_cover (L : Set Interval) (hL : IsClosed L)
      (hLf : (frontier L).Finite) :
      ∃ pieces : Finset (Interval × Interval),
        (∀ lr ∈ pieces, lr.1 ≤ lr.2) ∧ L = ⋃ lr ∈ pieces, Icc lr.1 lr.2 := by
    classical
    let E : Set Interval := frontier L ∪ {0,1}
    have hE : E.Finite := hLf.union (Set.toFinite _)
    let pieces := (hE.toFinset ×ˢ hE.toFinset).filter
      (fun lr => lr.1 ≤ lr.2 ∧ Icc lr.1 lr.2 ⊆ L)
    refine ⟨pieces,?_,?_⟩
    · intro lr hlr
      exact (Finset.mem_filter.mp hlr).2.1
    · apply Subset.antisymm
      · intro t ht
        by_cases htE : t ∈ E
        · refine mem_iUnion₂.mpr ⟨(t,t),?_,⟨le_rfl,le_rfl⟩⟩
          · apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_product.mpr ⟨hE.mem_toFinset.mpr htE,hE.mem_toFinset.mpr htE⟩,
              le_rfl,?_⟩
            intro z hz
            exact (le_antisymm hz.2 hz.1) ▸ ht
        · have ht0 : (0 : Interval) < t := by
            apply lt_of_le_of_ne bot_le
            intro h
            change (0 : Interval) = t at h
            exact htE (Or.inr (Or.inl h.symm))
          have ht1 : t < (1 : Interval) := by
            apply lt_of_le_of_ne le_top
            intro h
            change t = (1 : Interval) at h
            exact htE (Or.inr (Or.inr h))
          let lo := hE.toFinset.filter (fun z => z < t)
          let hi := hE.toFinset.filter (fun z => t < z)
          have hlo : lo.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨hE.mem_toFinset.mpr (Or.inr (by simp)),ht0⟩⟩
          have hhi : hi.Nonempty := ⟨1,Finset.mem_filter.mpr ⟨hE.mem_toFinset.mpr (Or.inr (by simp)),ht1⟩⟩
          let l := lo.max' hlo
          let r := hi.min' hhi
          have hl : l ∈ E ∧ l < t := by
            have hm := Finset.mem_filter.mp (Finset.max'_mem lo hlo)
            exact ⟨hE.mem_toFinset.mp hm.1,hm.2⟩
          have hr : r ∈ E ∧ t < r := by
            have hm := Finset.mem_filter.mp (Finset.min'_mem hi hhi)
            exact ⟨hE.mem_toFinset.mp hm.1,hm.2⟩
          have hgap : Disjoint (Ioo l r) (frontier L) := by
            apply disjoint_left.mpr
            intro z hz hzF
            have hzE : z ∈ E := Or.inl hzF
            rcases lt_trichotomy z t with hzt | rfl | htz
            · have hmem : z ∈ lo := Finset.mem_filter.mpr ⟨hE.mem_toFinset.mpr hzE,hzt⟩
              exact (not_lt_of_ge (Finset.le_max' lo z hmem)) hz.1
            · exact htE hzE
            · have hmem : z ∈ hi := Finset.mem_filter.mpr ⟨hE.mem_toFinset.mpr hzE,htz⟩
              exact (not_lt_of_ge (Finset.min'_le hi z hmem)) hz.2
          have hopen : Ioo l r ⊆ interior L := by
            apply isPreconnected_Ioo.subset_of_closure_inter_subset isOpen_interior
              ⟨t,⟨hl.2,hr.2⟩,(mem_interior_iff_notMem_frontier ht).mpr
                (fun hf => htE (Or.inl hf))⟩
            intro z hz
            have hzL : z ∈ L := closure_minimal interior_subset hL hz.1
            exact (mem_interior_iff_notMem_frontier hzL).mpr
              (fun hf => disjoint_left.mp hgap hz.2 hf)
          have hIcc : Icc l r ⊆ L := by
            rw [← closure_Ioo (hl.2.trans hr.2).ne]
            exact closure_minimal (hopen.trans interior_subset) hL
          refine mem_iUnion₂.mpr ⟨(l,r),?_,⟨hl.2.le,hr.2.le⟩⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨hE.mem_toFinset.mpr hl.1,hE.mem_toFinset.mpr hr.1⟩,
            (hl.2.trans hr.2).le,hIcc⟩
      · intro t ht
        obtain ⟨lr,hlr,htlr⟩ := mem_iUnion₂.mp ht
        exact (Finset.mem_filter.mp hlr).2.2 htlr
  have haffine_range (s t : Interval) :
      range (CurveComplex.BranchedDoubleCover.intervalAffine s t) =
      Icc (min s t) (max s t) := by
    let f := CurveComplex.BranchedDoubleCover.intervalAffine s t
    have hcont : Continuous f := by
      apply Continuous.subtype_mk
      change Continuous (fun u : Interval => (1-u.val)*s.val+u.val*t.val)
      fun_prop
    have hzero : f 0 = s := Subtype.ext (by
      simp [f,CurveComplex.BranchedDoubleCover.intervalAffine])
    have hone : f 1 = t := Subtype.ext (by
      simp [f,CurveComplex.BranchedDoubleCover.intervalAffine])
    apply Subset.antisymm
    · rintro z ⟨u,rfl⟩
      change (min s t).val ≤ (f u).val ∧ (f u).val ≤ (max s t).val
      have hsmin : (min s t).val ≤ s.val := min_le_left s t
      have htmin : (min s t).val ≤ t.val := min_le_right s t
      have hsmax : s.val ≤ (max s t).val := le_max_left s t
      have htmax : t.val ≤ (max s t).val := le_max_right s t
      change min s.val t.val ≤ s.val at hsmin
      change min s.val t.val ≤ t.val at htmin
      change s.val ≤ max s.val t.val at hsmax
      change t.val ≤ max s.val t.val at htmax
      have hLS := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr hsmin)
      have hLT := mul_nonneg u.property.1 (sub_nonneg.mpr htmin)
      have hUS := mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr hsmax)
      have hUT := mul_nonneg u.property.1 (sub_nonneg.mpr htmax)
      dsimp [f,CurveComplex.BranchedDoubleCover.intervalAffine]
      constructor <;> nlinarith
    · apply (isPreconnected_range hcont).Icc_subset
      · by_cases hst : s ≤ t
        · rw [min_eq_left hst]; exact ⟨0,hzero⟩
        · rw [min_eq_right (le_of_not_ge hst)]; exact ⟨1,hone⟩
      · by_cases hst : s ≤ t
        · rw [max_eq_right hst]; exact ⟨1,hone⟩
        · rw [max_eq_left (le_of_not_ge hst)]; exact ⟨0,hzero⟩
  have hfirstParam : range d.first =
      a (some v) '' Icc (min d.aStart d.aFinish) (max d.aStart d.aFinish) := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨_,haffine_range d.aStart d.aFinish ▸ mem_range_self t,(d.first_eq t).symm⟩
    · rintro ⟨t,ht,rfl⟩
      obtain ⟨u,hu⟩ := (haffine_range d.aStart d.aFinish).symm ▸ ht
      exact ⟨u,(d.first_eq u).trans (congrArg (a (some v)) hu)⟩
  have hsecondParam : range d.second =
      a (some w) '' Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨_,haffine_range d.bStart d.bFinish ▸ mem_range_self t,(d.second_eq t).symm⟩
    · rintro ⟨t,ht,rfl⟩
      obtain ⟨u,hu⟩ := (haffine_range d.bStart d.bFinish).symm ▸ ht
      exact ⟨u,(d.second_eq u).trans (congrArg (a (some w)) hu)⟩
  let δ : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun z => (d.disk z).val,continuous_subtype_val.comp d.disk.continuous⟩
  have hδ : Topology.IsEmbedding δ := Topology.IsEmbedding.subtypeVal.comp d.disk_embedded
  let K : Set S := range δ
  have hKclosed : IsClosed K := (isCompact_range δ.continuous).isClosed
  have hKsub (y : ↥F) : y.val ∈ K ↔ y ∈ range d.disk := by
    constructor
    · rintro ⟨z,hz⟩
      exact ⟨z,Subtype.ext hz⟩
    · rintro ⟨z,rfl⟩
      exact ⟨z,rfl⟩
  have hKfront : frontier K ⊆ Subtype.val ''
      (range d.first ∪ range d.second ∪ range d.boundarySide) := by
    intro y hy
    obtain ⟨z,hz,hzy⟩ :=
      (RegionalEmbeddedFamily.embedded_surface_disk_frontier_eq_boundary_image δ hδ) ▸ hy
    refine ⟨d.disk z,?_,hzy⟩
    exact d.boundary_image ▸ ⟨z,hz,rfl⟩
  have hpieces : ∀ i : Option ι, ∃ pieces : Finset (Interval × Interval),
      (∀ lr ∈ pieces, lr.1 ≤ lr.2) ∧
      range d.disk ∩ range (a i) = ⋃ lr ∈ pieces, a i '' Icc lr.1 lr.2 := by
    intro i
    by_cases hiv : i = some v
    · subst i
      refine ⟨{(min d.aStart d.aFinish,max d.aStart d.aFinish)},?_,?_⟩
      · intro lr hlr
        have he := Finset.mem_singleton.mp hlr
        rw [he]
        exact min_le_max
      · have hvwhole : range d.disk ∩ range (a (some v)) = range d.first := d.whole_first
        rw [hvwhole,hfirstParam]
        simp only [Finset.mem_singleton,Set.iUnion_iUnion_eq_left]
    · by_cases hiw : i = some w
      · subst i
        refine ⟨{(min d.bStart d.bFinish,max d.bStart d.bFinish)},?_,?_⟩
        · intro lr hlr
          have he := Finset.mem_singleton.mp hlr
          rw [he]
          exact min_le_max
        · have hwwhole : range d.disk ∩ range (a (some w)) = range d.second := d.whole_second
          rw [hwwhole,hsecondParam]
          simp only [Finset.mem_singleton,Set.iUnion_iUnion_eq_left]
      · have hifirst : (range d.first ∩ range (a i)).Finite :=
          (hfinite (some v) i (Ne.symm hiv)).subset (fun y hy => ⟨hfirst hy.1,hy.2⟩)
        have hisecond : (range d.second ∩ range (a i)).Finite :=
          (hfinite (some w) i (Ne.symm hiw)).subset (fun y hy => ⟨hsecond hy.1,hy.2⟩)
        have hiboundary : (range d.boundarySide ∩ range (a i)).Finite := by
          apply (Set.toFinite ({a i 0,a i 1} : Set ↥F)).subset
          rintro y ⟨⟨u,hu⟩,⟨t,ht⟩⟩
          have hyt : ((a i) t).val ∈ frontier F := by
            rw [ht,← hu]
            exact hBFront (d.boundary_in_B u)
          by_cases ht0 : t = 0
          · exact Or.inl (ht0 ▸ ht.symm)
          · by_cases ht1 : t = 1
            · exact Or.inr (ht1 ▸ ht.symm)
            · exact False.elim ((hproper i).2.2.2 t
                ⟨lt_of_le_of_ne bot_le (Ne.symm ht0),lt_of_le_of_ne le_top ht1⟩ hyt)
        have hsidefinite : ((range d.first ∪ range d.second ∪ range d.boundarySide) ∩
            range (a i)).Finite := by
          rw [Set.union_inter_distrib_right,Set.union_inter_distrib_right]
          exact (hifirst.union hisecond).union hiboundary
        let f : C(Interval,S) := ⟨fun t => ((a i) t).val,
          continuous_subtype_val.comp (a i).continuous⟩
        have hfi : Function.Injective f := fun t u he =>
          (hproper i).1.injective (Subtype.ext he)
        have hfrontfinite : (frontier K ∩ range f).Finite := by
          apply (hsidefinite.image Subtype.val).subset
          rintro y ⟨hy,⟨t,ht⟩⟩
          obtain ⟨z,hz,hzy⟩ := hKfront hy
          refine ⟨z,⟨hz,?_⟩,hzy⟩
          exact ⟨t,Subtype.ext (ht.trans hzy.symm)⟩
        have hLf : (frontier (f ⁻¹' K)).Finite := by
          apply (hfrontfinite.preimage hfi.injOn).subset
          intro t ht
          exact ⟨f.continuous.frontier_preimage_subset K ht,mem_range_self t⟩
        obtain ⟨P,hPorder,hP⟩ := hfinite_interval_cover (f ⁻¹' K)
          (hKclosed.preimage f.continuous) hLf
        refine ⟨P,hPorder,?_⟩
        ext y
        constructor
        · rintro ⟨hy,⟨t,rfl⟩⟩
          have ht : t ∈ f ⁻¹' K := (hKsub _).mpr hy
          obtain ⟨lr,hlr,htlr⟩ := mem_iUnion₂.mp (hP ▸ ht)
          exact mem_iUnion₂.mpr ⟨lr,hlr,t,htlr,rfl⟩
        · intro hy
          obtain ⟨lr,hlr,t,ht,rfl⟩ := mem_iUnion₂.mp hy
          refine ⟨(hKsub _).mp ?_,mem_range_self t⟩
          change t ∈ f ⁻¹' K
          rw [hP]
          exact mem_iUnion₂.mpr ⟨lr,hlr,ht⟩
  let events := contactSites F a {some v,some w} (range d.first ∪ range d.second) V
  have heventInterior (p : ↥events) : p.val.val ∈ interior F := by
    obtain ⟨hpV,hps,i,hi,j,hij,hpij⟩ := p.property
    exact hcontact_interior i j hij p.val hpij.1 hpij.2
  have hcenters (p : ↥events) (i : incidentIndex a p.val) :
      ∃ t : Interval, t ∈ Ioo (0 : Interval) 1 ∧ a i.val t = p.val := by
    obtain ⟨t,ht⟩ := i.property
    refine ⟨t,?_,ht⟩
    have hnot : ((a i.val) t).val ∉ frontier F := by
      rw [ht]
      exact fun h => Set.disjoint_left.mp disjoint_interior_frontier (heventInterior p) h
    have ht0 : t ≠ 0 := by
      intro he
      exact hnot (he.symm ▸ hBFront (hproper i.val).2.1)
    have ht1 : t ≠ 1 := by
      intro he
      exact hnot (he.symm ▸ hBFront (hproper i.val).2.2.1)
    exact ⟨lt_of_le_of_ne bot_le ht0.symm,lt_of_le_of_ne le_top ht1⟩
  have hactualCross (p : ↥events) (i j : Option ι) (hij : i ≠ j)
      (u t : Interval) (hu : u ∈ Ioo (0 : Interval) 1)
      (ht : t ∈ Ioo (0 : Interval) 1) (hip : a i u = p.val) (hjp : a j t = p.val) :
      ∃ C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F (a i) (a j) u t,
        C.OppositeSides := hcross i j hij u t hu ht (hip.trans hjp.symm)
  choose pieces piece_order whole_trace_pieces using hpieces
  have hgeometry :
      ∃ window : ∀ p : ↥events, IncidentFanWindow F a V p.val,
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
    exact regional_paired_half_disk_fan_window_geometry S g hg hS x R hR htarget
      F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
      ι r α hinv hcross v w hvw d V hV hdV havoid
  obtain ⟨window,hwindowDisjoint,hselectedAxis,hcrossV⟩ := hgeometry
  have hfan : Nonempty (FiniteFanCarrier F
      (augmented (fun i => (r i).val.val) α.val.val) {some v,some w}
      (range d.first ∪ range d.second) V (range d.disk)
      (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v)) :=
    ⟨{ events := events
       events_finite := hevents
       events_exact := rfl
       pieces := pieces
       piece_order := piece_order
       whole_trace_pieces := whole_trace_pieces
       carrier_in_V := hdV
       forbidden_finite := hforbidden
       window := window
       windows_disjoint := hwindowDisjoint
       selected_axis_fans := hselectedAxis
       opposite_side_charts := hcrossV }⟩
  refine ⟨hfan,hαfirst,hαsecond,?_⟩
  intro j hjv hjw
  obtain ⟨hpart,hdPQ,hdPC,hdQC,hPF,hQF,hCF,hcard⟩ :=
    hpartition (range (r v).val.val) (range (r j).val.val)
      (range d.first) C₀ hfirst hcorner (hinv.1 v j hjv.symm)
  refine ⟨hpart,hdPQ,hdPC,hdQC,hPF,?_,hQF,hCF,hcard⟩
  exact (hinv.1 w j hjw.symm).subset (fun y hy => ⟨hsecond hy.1.1,hy.2⟩)
