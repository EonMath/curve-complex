import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalStripPushOff
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualStripNarrowing
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip

open CurveComplex Set Topology

theorem regional_strip_narrow_open_core
    {S : Type} [TopologicalSpace S]
    (F Q : Set S) (hFQ : F ⊆ Q)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1, ↥Q))
    (hE : Topology.IsEmbedding E)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (N : C(Interval × Set.Icc (-1 : ℝ) 1, ↥F))
    (htrace : ∀ z, (N z).val =
      (E (z.1,⟨δ * (z.2 : ℝ),by
        constructor <;> nlinarith
          [z.2.property.1,z.2.property.2,hδ,hδ1]⟩)).val) :
    IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
  have hW : IsOpen {z : Interval × Set.Icc (-1 : ℝ) 1 |
      -δ < z.2.val ∧ z.2.val < δ} :=
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
  obtain ⟨O,hO,himage⟩ := hE.isInducing.image_eq_isOpen_inter_range hW
  have hQopen : IsOpen (E '' {z | -δ < z.2.val ∧ z.2.val < δ}) := by
    have heq : E '' {z | -δ < z.2.val ∧ z.2.val < δ} =
        O ∩ E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
      apply Set.Subset.antisymm
      · intro y hy
        have hOy := (himage ▸ hy).1
        obtain ⟨z,hz,rfl⟩ := hy
        exact ⟨hOy,⟨z,⟨by linarith [hz.1],by linarith [hz.2]⟩,rfl⟩⟩
      · rintro y ⟨hy,z,hz,rfl⟩
        rw [himage]
        exact ⟨hy,Set.mem_range_self z⟩
    rw [heq]
    exact hO.inter hopen
  let inc : C(↥F,↥Q) :=
    ⟨fun y => ⟨y.val,hFQ y.property⟩,continuous_subtype_val.subtype_mk _⟩
  have heq : inc ⁻¹' (E '' {z | -δ < z.2.val ∧ z.2.val < δ}) =
      N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
    ext y
    constructor
    · rintro ⟨⟨t,v⟩,hv,he⟩
      have hlo : -1 < (v : ℝ)/δ :=
        (lt_div_iff₀ hδ).mpr (by linarith [hv.1])
      have hhi : (v : ℝ)/δ < 1 :=
        (div_lt_iff₀ hδ).mpr (by linarith [hv.2])
      let w : Set.Icc (-1 : ℝ) 1 := ⟨(v : ℝ)/δ,⟨hlo.le,hhi.le⟩⟩
      have hscale : δ * (w : ℝ) = (v : ℝ) := by
        change δ * ((v : ℝ)/δ) = (v : ℝ)
        field_simp
      have hvalue : (N (t,w)).val = (E (t,v)).val := by
        rw [htrace]
        apply congrArg (fun z => (E z).val)
        apply Prod.ext
        · rfl
        · exact Subtype.ext hscale
      exact ⟨(t,w),⟨hlo,hhi⟩,
        Subtype.ext (hvalue.trans (congrArg Subtype.val he))⟩
    · rintro ⟨⟨t,w⟩,hw,rfl⟩
      let v : Set.Icc (-1 : ℝ) 1 := ⟨δ*(w : ℝ),by
        constructor <;> nlinarith
          [w.property.1,w.property.2,hδ,hδ1]⟩
      refine ⟨(t,v),?_,?_⟩
      · constructor <;> nlinarith [hw.1,hw.2]
      · apply Subtype.ext
        exact (htrace (t,w)).symm
  rw [← heq]
  exact hQopen.preimage inc.continuous

/-- A Q-strip whose center lies in the region and avoids every retained
    frontier component narrows to an actual proper strip in the same `F`.
    The interior slab stays in `interior F` by connectedness and frontier
    avoidance. -/
theorem regional_narrow_Q_strip_into_F
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F Q B G : Set S) (hFQ : F ⊆ Q)
    (hF : IsClosed F) (hG : IsClosed G)
    (hBF : B ⊆ F) (hfront : frontier F ⊆ B ∪ G)
    (a : C(Interval, ↥F))
    (haI : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (a t).val ∈ interior F)
    (hacle : ∀ t, (a t).val ∉ G)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1, ↥Q))
    (hE : Topology.IsEmbedding E)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (hcenter : ∀ t, (E (t,⟨0,by norm_num⟩)).val = (a t).val)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∉ B) :
    ∃ N : C(Interval × Set.Icc (-1 : ℝ) 1, ↥F),
      Topology.IsEmbedding N ∧
      (∀ t, N (t,⟨0,by norm_num⟩) = a t) ∧
      (∀ w, (N (0,w)).val ∈ B ∧ (N (1,w)).val ∈ B) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
        (N (t,w)).val ∈ interior F) ∧
      (∀ z, (N z).val ∉ G) ∧
      IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
  let raw : C(Interval × Set.Icc (-1 : ℝ) 1,S) :=
    ⟨fun z => (E z).val, continuous_subtype_val.comp E.continuous⟩
  have hraw : Topology.IsEmbedding raw := Topology.IsEmbedding.subtypeVal.comp hE
  obtain ⟨ρ,hρ,n,hn,hnclear,hnformula,hncenter⟩ :=
    source_shrink_embedded_strip_in_open raw hraw Gᶜ hG.isOpen_compl
      (by intro t; change (E (t,⟨0,by norm_num⟩)).val ∉ G
          rw [hcenter]; exact hacle t)
  have hnend : ∀ w, n (0,w) ∈ B ∧ n (1,w) ∈ B := by
    intro w
    rw [hnformula,hnformula]
    exact hend _
  have hnoB : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      n (t,w) ∉ B := by
    intro t ht w
    rw [hnformula]
    exact hint t ht _
  let U : Set S := n '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.univ)
  let : ConnectedSpace (Set.Icc (-1 : ℝ) 1) :=
    Subtype.connectedSpace (isConnected_Icc (by norm_num : (-1 : ℝ) ≤ 1))
  have hUp : IsPreconnected U :=
    (isPreconnected_Ioo.prod isPreconnected_univ).image n hn.continuous.continuousOn
  have hUoff : Disjoint U (frontier F) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨⟨t,w⟩,ht,rfl⟩ hy
    rcases hfront hy with hB | hG'
    · exact hnoB t ht.1 w hB
    · exact hnclear (Set.mem_range_self _) hG'
  let tm : Interval := ⟨1/2,by norm_num⟩
  have htm : tm ∈ Set.Ioo (0 : Interval) 1 := by
    constructor
    · change (0 : ℝ) < 1/2
      norm_num
    · change (1/2 : ℝ) < 1
      norm_num
  have hmid : n (tm,⟨0,by norm_num⟩) = (a tm).val :=
    (hncenter tm).trans (hcenter tm)
  have hUne : ∃ y ∈ U, y ∈ interior F :=
    ⟨n (tm,⟨0,by norm_num⟩),
      ⟨(tm,⟨0,by norm_num⟩),⟨htm,trivial⟩,rfl⟩,
      hmid.symm ▸ haI tm htm⟩
  obtain ⟨y,hyU,hyF⟩ := hUne
  have hUI : U ⊆ interior F := by
    apply hUp.subset_of_closure_inter_subset isOpen_interior ⟨y,hyU,hyF⟩
    intro z hz
    have hzF : z ∈ F := closure_minimal interior_subset hF hz.1
    by_contra hn'
    exact Set.disjoint_left.mp hUoff hz.2
      ((mem_frontier_iff_notMem_interior hzF).mpr hn')
  have hnI : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      n (t,w) ∈ interior F := by
    intro t ht w
    exact hUI ⟨(t,w),⟨ht,trivial⟩,rfl⟩
  have hnF : ∀ z, n z ∈ F := by
    intro z
    by_cases hz0 : z.1 = 0
    · apply hBF
      change n (z.1,z.2) ∈ B
      rw [hz0]
      exact (hnend z.2).1
    by_cases hz1 : z.1 = 1
    · apply hBF
      change n (z.1,z.2) ∈ B
      rw [hz1]
      exact (hnend z.2).2
    exact interior_subset
      (hnI z.1 ⟨bot_lt_iff_ne_bot.mpr hz0,
        lt_top_iff_ne_top.mpr hz1⟩ z.2)
  let N : C(Interval × Set.Icc (-1 : ℝ) 1,↥F) :=
    ⟨fun z => ⟨n z,hnF z⟩,hn.continuous.subtype_mk _⟩
  have hN : Topology.IsEmbedding N := hn.codRestrict _ hnF
  have hNopen := regional_strip_narrow_open_core F Q hFQ E hE hopen
    ρ hρ.1 hρ.2 N hnformula
  refine ⟨N,hN,?_,hnend,hnI,?_,hNopen⟩
  · intro t
    apply Subtype.ext
    exact (hncenter t).trans (hcenter t)
  · intro z
    exact hnclear (Set.mem_range_self z)

#print axioms regional_narrow_Q_strip_into_F
