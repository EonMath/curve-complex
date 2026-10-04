import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalFStripNarrowing

open CurveComplex Set Topology

/-- Every literal proper arc in the approved original region has an actual
    two-ended strip in that same `F`, avoiding all retained frontier curves. -/
theorem regional_original_proper_arc_has_F_strip
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image)
    (a : C(Interval, ↥F)) (ha : Topology.IsEmbedding a)
    (h0 : (a 0).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (h1 : (a 1).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (a t).val ∉ frontier F) :
    let B : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    ∃ N : C(Interval × Set.Icc (-1 : ℝ) 1, ↥F),
      Topology.IsEmbedding N ∧
      (∀ t, N (t,⟨0,by norm_num⟩) = a t) ∧
      (∀ w, (N (0,w)).val ∈ B ∧ (N (1,w)).val ∈ B) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
        (N (t,w)).val ∈ interior F) ∧
      IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
  let : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  let B : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
  let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
  let G : Set S := ⋃ i, (c i).val.image
  let inclusion : C(↥F,↥Q) :=
    ⟨fun y => ⟨y.val,houtside y.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hi : Topology.IsEmbedding inclusion := by
    apply Topology.IsEmbedding.of_comp inclusion.continuous continuous_subtype_val
    exact Topology.IsEmbedding.subtypeVal
  have hBF : B ⊆ frontier F := by
    rw [hfrontier]
    exact Set.subset_union_left
  let qa : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨inclusion.comp a,hi.comp ha,h0,h1,
      (fun t ht hb => hproper t ht (hBF hb))⟩
  obtain ⟨E,hE,hcenter,hend,hint,hopen⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget qa
  have hG : IsClosed G :=
    (isCompact_iUnion (fun i => isCompact_range (c i).val.embedded.continuous)).isClosed
  have haI : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (a t).val ∈ interior F := by
    intro t ht
    exact (mem_interior_iff_notMem_frontier (a t).property).mpr (hproper t ht)
  have hacle : ∀ t, (a t).val ∉ G := by
    intro t ht
    obtain ⟨i,hi'⟩ := Set.mem_iUnion.mp ht
    by_cases ht0 : t = 0
    · exact Set.disjoint_left.mp (hbaseDisjoint i) hi' (ht0 ▸ h0)
    by_cases ht1 : t = 1
    · exact Set.disjoint_left.mp (hbaseDisjoint i) hi' (ht1 ▸ h1)
    apply hproper t ⟨bot_lt_iff_ne_bot.mpr ht0,
      lt_top_iff_ne_top.mpr ht1⟩
    rw [hfrontier]
    exact Or.inr (Set.mem_iUnion.mpr ⟨i,hi'⟩)
  obtain ⟨N,hN,hNc,hNend,hNint,hNclear,hNopen⟩ :=
    regional_narrow_Q_strip_into_F F Q B G houtside hFcompact.isClosed hG
      hbase (by rw [hfrontier]) a haI hacle E hE
      hopen (fun t => congrArg Subtype.val (hcenter t)) hend hint
  exact ⟨N,hN,hNc,hNend,hNint,hNopen⟩

#print axioms regional_original_proper_arc_has_F_strip

/-- The actual original-region collar supplies two disjoint, supported proper
    push-offs of any proper regional arc, inside every open neighborhood of it. -/
theorem regional_original_proper_arc_two_supported_push_offs
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image)
    (a : C(Interval, ↥F)) (ha : Topology.IsEmbedding a)
    (h0 : (a 0).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (h1 : (a 1).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)
    (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (a t).val ∉ frontier F)
    (O : Set ↥F) (hO : IsOpen O) (haO : Set.range a ⊆ O) :
    ∃ p q : C(Interval, ↥F),
      Topology.IsEmbedding p ∧ Topology.IsEmbedding q ∧
      (p 0).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
      (p 1).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
      (q 0).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
      (q 1).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (p t).val ∉ frontier F) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (q t).val ∉ frontier F) ∧
      Set.range p ⊆ O ∧ Set.range q ⊆ O ∧
      Disjoint (Set.range p) (Set.range a) ∧
      Disjoint (Set.range q) (Set.range a) ∧
      Disjoint (Set.range p) (Set.range q) ∧
      ∃ H K : C(Interval × Interval, ↥F),
        (∀ t, H (0,t) = a t ∧ K (0,t) = a t) ∧
        (∀ t, H (1,t) = p t ∧ K (1,t) = q t) ∧
        (∀ s, Topology.IsEmbedding (fun t : Interval => H (s,t)) ∧
          Topology.IsEmbedding (fun t : Interval => K (s,t))) ∧
        (∀ s, (H (s,0)).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
          (H (s,1)).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
          (K (s,0)).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∧
          (K (s,1)).val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
          Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R) := by
  let : ClosedSurface S := Classical.choice hS.2.1
  obtain ⟨N,hN,hNc,hNend,hNint,hNopen⟩ :=
    regional_original_proper_arc_has_F_strip S g hg hS x R hR htarget
      F hFcompact hbase houtside J c hbaseDisjoint hfrontier
      a ha h0 h1 hproper
  let B : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
  obtain ⟨p,q,hp,hq,hp0,hp1,hq0,hq1,hpi,hqi,hpO,hqO,hdpa,hdqa,hdpq,
    wp,wm,hpw,hqw⟩ := regional_embedded_proper_strip_two_supported_push_offs F B a N hN
    hNc hNend
    (fun t ht w hf =>
      (mem_interior_iff_notMem_frontier
        (interior_subset (hNint t ht w))).mp (hNint t ht w) hf)
    O hO haO
  obtain ⟨H,hH0,hH1,hHemb,hHend,hHint⟩ :=
    regional_embedded_strip_constant_width_family F B a N hN hNc hNend
      (fun t ht w hf =>
        (mem_interior_iff_notMem_frontier
          (interior_subset (hNint t ht w))).mp (hNint t ht w) hf) wp
  obtain ⟨K,hK0,hK1,hKemb,hKend,hKint⟩ :=
    regional_embedded_strip_constant_width_family F B a N hN hNc hNend
      (fun t ht w hf =>
        (mem_interior_iff_notMem_frontier
          (interior_subset (hNint t ht w))).mp (hNint t ht w) hf) wm
  refine ⟨p,q,hp,hq,hp0,hp1,hq0,hq1,hpi,hqi,hpO,hqO,hdpa,hdqa,hdpq,
    H,K,?_,?_,?_,?_⟩
  · intro t
    exact ⟨hH0 t,hK0 t⟩
  · intro t
    exact ⟨(hH1 t).trans (hpw t).symm,
      (hK1 t).trans (hqw t).symm⟩
  · intro s
    exact ⟨hHemb s,hKemb s⟩
  · intro s
    exact ⟨(hHend s).1,(hHend s).2,(hKend s).1,(hKend s).2⟩

#print axioms regional_original_proper_arc_two_supported_push_offs
