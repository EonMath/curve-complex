import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

private theorem embedded_disk_boundary_is_curve
    {X : Type} [TopologicalSpace X] [T2Space X]
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, X))
    (hd : Topology.IsEmbedding d) :
    ∃ c : CurveComplex.Curve X,
      c.image = d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  let ι : Circle → Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun z => ⟨Complex.orthonormalBasisOneI.repr (z : ℂ), by
      apply Metric.mem_closedBall.mpr
      simpa only [dist_zero_right] using
        ((Complex.orthonormalBasisOneI.repr.norm_map (z : ℂ)).trans z.norm_coe).le⟩
  have hιcont : Continuous ι :=
    (Complex.orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val).subtype_mk _
  have hιinj : Function.Injective ι := by
    intro z w h
    apply Subtype.ext
    apply Complex.orthonormalBasisOneI.repr.injective
    exact congrArg Subtype.val h
  have hι : Topology.IsEmbedding ι := (hιcont.isClosedEmbedding hιinj).isEmbedding
  let c : CurveComplex.Curve X := ⟨d ∘ ι, hd.comp hι⟩
  have hιrange : Set.range ι =
      {z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      simp [ι]
    · intro hz
      have hz' : ‖z.val‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hz
      let w : Circle := ⟨Complex.orthonormalBasisOneI.repr.symm z.val, by
        change Complex.orthonormalBasisOneI.repr.symm z.val ∈ Metric.sphere (0 : ℂ) 1
        simpa only [Metric.mem_sphere, dist_zero_right] using
          ((Complex.orthonormalBasisOneI.repr.symm.norm_map z.val).trans hz')⟩
      refine ⟨w, ?_⟩
      apply Subtype.ext
      exact Complex.orthonormalBasisOneI.repr.apply_symm_apply z.val
  refine ⟨c, ?_⟩
  change Set.range (d ∘ ι) = _
  rw [Set.range_comp, hιrange]

private theorem curve_image_has_no_cutpoint
    {X : Type} [TopologicalSpace X] [T2Space X]
    (c : CurveComplex.Curve X) (z : Circle) :
    IsPreconnected (c.image \ {c.map z}) := by
  have hconnected : IsPreconnected ({z}ᶜ : Set Circle) :=
    (Circle.isPathConnected_compl_singleton z).isConnected.isPreconnected
  have himage : c.map '' ({z}ᶜ : Set Circle) = c.image \ {c.map z} := by
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_sdiff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, rfl⟩, c.embedded.injective.ne hw⟩
    · rintro ⟨⟨w, rfl⟩, hw⟩
      exact ⟨w, fun h => hw (congrArg c.map h), rfl⟩
  rw [← himage]
  exact hconnected.image c.map c.embedded.continuous.continuousOn

private theorem arc_meets_boundary_arc_only_at_endpoints
    {X : Type} [TopologicalSpace X]
    (B : Set X) (a b : C(CurveComplex.Interval, X))
    (haInt : ∀ t ∈ Set.Ioo (0 : CurveComplex.Interval) 1, a t ∉ B)
    (hbB : Set.range b ⊆ B) :
    Set.range a ∩ Set.range b ⊆ {a 0, a 1} := by
  rintro x ⟨⟨t, rfl⟩, htb⟩
  have hB : a t ∈ B := hbB htb
  by_cases ht0 : t = 0
  · simp [ht0]
  by_cases ht1 : t = 1
  · simp [ht1]
  have ht : t ∈ Set.Ioo (0 : CurveComplex.Interval) 1 := by
    constructor
    · exact lt_of_le_of_ne t.property.1 (Ne.symm ht0)
    · exact lt_of_le_of_ne t.property.2 ht1
  exact False.elim ((haInt t ht) hB)

private theorem endpoint_mem_other_of_punctured_preconnected
    {X : Type} [TopologicalSpace X]
    (A C : Set X) (u v : X)
    (hA : IsClosed A) (hC : IsClosed C)
    (hu : u ∈ A) (huv : u ≠ v)
    (hCnontrivial : ∃ x ∈ C, x ≠ v)
    (hmeet : A ∩ C ⊆ {u, v})
    (hcut : IsPreconnected ((A ∪ C) \ {v})) :
    u ∈ C := by
  by_contra huc
  have hinter : ((A ∪ C) \ {v}) ∩ (A ∩ C) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, hxv⟩, hxA, hxC⟩
    rcases hmeet ⟨hxA, hxC⟩ with hxu | hxv'
    · exact huc (hxu ▸ hxC)
    · exact hxv hxv'
  have hcover : (A ∪ C) \ {v} ⊆ A ∪ C := Set.sdiff_subset
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hcut)
      A C hA hC hcover hinter with hsubA | hsubC
  · obtain ⟨x, hxC, hxv⟩ := hCnontrivial
    have hxAC : x ∈ A := hsubA ⟨Or.inr hxC, hxv⟩
    rcases hmeet ⟨hxAC, hxC⟩ with hxu | hxv'
    · exact huc (hxu ▸ hxC)
    · exact hxv hxv'
  · exact huc (hsubC ⟨Or.inl hu, huv⟩)

private theorem both_arc_endpoints_lie_in_other_of_no_cutpoint
    {X : Type} [TopologicalSpace X] [T2Space X]
    (a b : C(CurveComplex.Interval, X))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (hmeet : Set.range a ∩ Set.range b ⊆ {a 0, a 1})
    (hcut0 : IsPreconnected ((Set.range a ∪ Set.range b) \ {a 0}))
    (hcut1 : IsPreconnected ((Set.range a ∪ Set.range b) \ {a 1})) :
    a 0 ∈ Set.range b ∧ a 1 ∈ Set.range b := by
  have hA : IsClosed (Set.range a) := (isCompact_range a.continuous).isClosed
  have hC : IsClosed (Set.range b) := (isCompact_range b.continuous).isClosed
  have ha01 : a 0 ≠ a 1 := by
    intro h
    exact zero_ne_one (ha.injective h)
  have hb01 : b 0 ≠ b 1 := by
    intro h
    exact zero_ne_one (hb.injective h)
  have hnon (v : X) : ∃ x ∈ Set.range b, x ≠ v := by
    by_cases h : b 0 = v
    · exact ⟨b 1, ⟨1, rfl⟩, by simpa [h] using hb01.symm⟩
    · exact ⟨b 0, ⟨0, rfl⟩, h⟩
  constructor
  · exact endpoint_mem_other_of_punctured_preconnected
      (Set.range a) (Set.range b) (a 0) (a 1) hA hC
      ⟨0, rfl⟩ ha01 (hnon _) hmeet hcut1
  · exact endpoint_mem_other_of_punctured_preconnected
      (Set.range a) (Set.range b) (a 1) (a 0) hA hC
      ⟨1, rfl⟩ ha01.symm (hnon _) (by simpa [Set.pair_comm] using hmeet) hcut0

private theorem closed_two_piece_cut_impossible
    {X : Type} [TopologicalSpace X]
    (A P Q : Set X) (u v w : X)
    (hA : IsClosed A) (hP : IsClosed P) (hQ : IsClosed Q)
    (hvA : v ∈ A) (hvQ : v ∉ Q) (hvu : v ≠ u)
    (hwQ : w ∈ Q) (hwA : w ∉ A) (hwP : w ∉ P) (hwu : w ≠ u)
    (hmeet : (A ∪ P) ∩ Q ⊆ {u})
    (hcut : IsPreconnected (((A ∪ P) ∪ Q) \ {u})) : False := by
  have hempty : (((A ∪ P) ∪ Q) \ {u}) ∩ ((A ∪ P) ∩ Q) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, hxu⟩, hx⟩
    exact hxu (hmeet hx)
  have hsub : ((A ∪ P) ∪ Q) \ {u} ⊆ (A ∪ P) ∪ Q := Set.sdiff_subset
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hcut)
      (A ∪ P) Q (hA.union hP) hQ hsub hempty with hleft | hright
  · rcases hleft ⟨Or.inr hwQ, hwu⟩ with hwa | hwp
    · exact hwA hwa
    · exact hwP hwp
  · exact hvQ (hright ⟨Or.inl (Or.inl hvA), hvu⟩)

private theorem shared_endpoint_cannot_be_inside_other_arc
    {X : Type} [TopologicalSpace X] [T2Space X]
    (A : Set X) (b : C(CurveComplex.Interval, X))
    (hA : IsClosed A) (hb : Topology.IsEmbedding b)
    (u v : X) (huv : u ≠ v) (hvA : v ∈ A)
    (hmeet : A ∩ Set.range b ⊆ {u, v})
    (hcut : IsPreconnected ((A ∪ Set.range b) \ {u}))
    (huB : u ∈ Set.range b) (hvB : v ∈ Set.range b) :
    u = b 0 ∨ u = b 1 := by
  obtain ⟨t, ht⟩ := huB
  obtain ⟨s, hs⟩ := hvB
  have hst : s ≠ t := by
    intro h
    exact huv (ht.symm.trans (h ▸ hs))
  by_cases ht0 : t = 0
  · exact Or.inl (ht.symm.trans (congrArg b ht0))
  by_cases ht1 : t = 1
  · exact Or.inr (ht.symm.trans (congrArg b ht1))
  have htpos : 0 < t := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  have htlt : t < 1 := lt_of_le_of_ne t.property.2 ht1
  let L : Set X := b '' Set.Icc (0 : CurveComplex.Interval) t
  let R : Set X := b '' Set.Icc t (1 : CurveComplex.Interval)
  have hLclosed : IsClosed L := (isCompact_Icc.image b.continuous).isClosed
  have hRclosed : IsClosed R := (isCompact_Icc.image b.continuous).isClosed
  have hLsub : L ⊆ Set.range b := Set.image_subset_range _ _
  have hRsub : R ⊆ Set.range b := Set.image_subset_range _ _
  have hLmem (r : CurveComplex.Interval) (hr : r ≤ t) : b r ∈ L :=
    ⟨r, ⟨r.property.1, hr⟩, rfl⟩
  have hRmem (r : CurveComplex.Interval) (hr : t ≤ r) : b r ∈ R :=
    ⟨r, ⟨hr, r.property.2⟩, rfl⟩
  have hrange : Set.range b = L ∪ R := by
    apply Set.Subset.antisymm
    · rintro x ⟨r, rfl⟩
      rcases le_total r t with h | h
      · exact Or.inl (hLmem r h)
      · exact Or.inr (hRmem r h)
    · exact Set.union_subset hLsub hRsub
  have hLR : L ∩ R ⊆ {u} := by
    rintro x ⟨⟨r, hr, rfl⟩, ⟨q, hq, heq⟩⟩
    have hrq : r = q := hb.injective heq.symm
    have hrt : r = t := le_antisymm hr.2 (hrq ▸ hq.1)
    simp [hrt, ht]
  have hcut' : IsPreconnected (((A ∪ L) ∪ R) \ {u}) := by
    simpa only [hrange, Set.union_assoc] using hcut
  rcases lt_or_gt_of_ne hst with hst' | hts'
  · have hvR : v ∉ R := by
      rintro ⟨r, hr, heq⟩
      have hrs : r = s := hb.injective (heq.trans hs.symm)
      exact (not_le_of_gt hst') (hrs ▸ hr.1)
    have hmeetR : (A ∪ L) ∩ R ⊆ {u} := by
      rintro x ⟨hx, hxR⟩
      rcases hx with hxA | hxL
      · rcases hmeet ⟨hxA, hRsub hxR⟩ with hxu | hxv
        · exact hxu
        · exact False.elim (hvR (hxv ▸ hxR))
      · exact hLR ⟨hxL, hxR⟩
    have hwA : b 1 ∉ A := by
      intro hwA
      rcases hmeet ⟨hwA, ⟨1, rfl⟩⟩ with hwu | hwv
      · exact ht1 (hb.injective (ht.trans hwu.symm))
      · have h1s : (1 : CurveComplex.Interval) = s := hb.injective (hwv.trans hs.symm)
        exact (ne_of_lt (hst'.trans_le t.property.2)) h1s.symm
    have hwL : b 1 ∉ L := by
      rintro ⟨r, hr, heq⟩
      have h1r : (1 : CurveComplex.Interval) = r := hb.injective heq.symm
      exact (not_le_of_gt htlt) (h1r ▸ hr.2)
    exact False.elim (closed_two_piece_cut_impossible A L R u v (b 1)
      hA hLclosed hRclosed hvA hvR huv.symm
      (hRmem 1 t.property.2) hwA hwL
      (by intro h; exact ht1 (hb.injective (ht.trans h.symm))) hmeetR hcut')
  · have hcut'' : IsPreconnected (((A ∪ R) ∪ L) \ {u}) := by
      rw [hrange, Set.union_comm L R] at hcut
      simpa only [Set.union_assoc] using hcut
    have hvL : v ∉ L := by
      rintro ⟨r, hr, heq⟩
      have hrs : r = s := hb.injective (heq.trans hs.symm)
      exact (not_le_of_gt hts') (hrs ▸ hr.2)
    have hmeetL : (A ∪ R) ∩ L ⊆ {u} := by
      rintro x ⟨hx, hxL⟩
      rcases hx with hxA | hxR
      · rcases hmeet ⟨hxA, hLsub hxL⟩ with hxu | hxv
        · exact hxu
        · exact False.elim (hvL (hxv ▸ hxL))
      · exact hLR ⟨hxL, hxR⟩
    have hwA : b 0 ∉ A := by
      intro hwA
      rcases hmeet ⟨hwA, ⟨0, rfl⟩⟩ with hwu | hwv
      · exact ht0 (hb.injective (ht.trans hwu.symm))
      · have h0s : (0 : CurveComplex.Interval) = s := hb.injective (hwv.trans hs.symm)
        exact (ne_of_gt (htpos.trans hts')) h0s.symm
    have hwR : b 0 ∉ R := by
      rintro ⟨r, hr, heq⟩
      have h0r : (0 : CurveComplex.Interval) = r := hb.injective heq.symm
      exact (not_le_of_gt htpos) (h0r ▸ hr.1)
    exact False.elim (closed_two_piece_cut_impossible A R L u v (b 0)
      hA hRclosed hLclosed hvA hvL huv.symm
      (hLmem 0 t.property.1) hwA hwR
      (by intro h; exact ht0 (hb.injective (ht.trans h.symm))) hmeetL hcut'')

theorem actual_disk_boundary_two_arcs_forces_endpoint_orientation
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (a b : C(CurveComplex.Interval,X))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (ha0 : a 0 ∈ B) (ha1 : a 1 ∈ B)
    (haInt : ∀ t ∈ Set.Ioo (0 : CurveComplex.Interval) 1,a t ∉ B)
    (hbB : Set.range b ⊆ B)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,X))
    (hd : Topology.IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      Set.range a ∪ Set.range b) :
    (b 0=a 0 ∧ b 1=a 1) ∨ (b 0=a 1 ∧ b 1=a 0) := by
  have _hboundaryEndpoints : a 0 ∈ B ∧ a 1 ∈ B := ⟨ha0, ha1⟩
  have hmeet : Set.range a ∩ Set.range b ⊆ {a 0, a 1} :=
    arc_meets_boundary_arc_only_at_endpoints B a b haInt hbB
  have ha01 : a 0 ≠ a 1 := by
    intro h
    have h01 : (0 : CurveComplex.Interval) = 1 := ha.injective h
    exact zero_ne_one h01
  obtain ⟨c, hc⟩ := embedded_disk_boundary_is_curve d hd
  have hcover : c.image = Set.range a ∪ Set.range b := hc.trans hboundary
  have hcut (i : CurveComplex.Interval) :
      IsPreconnected ((Set.range a ∪ Set.range b) \ {a i}) := by
    have hi : a i ∈ c.image := by
      rw [hcover]
      exact Or.inl ⟨i, rfl⟩
    obtain ⟨z, hz⟩ := hi
    rw [← hcover, ← hz]
    exact curve_image_has_no_cutpoint c z
  have hends : a 0 ∈ Set.range b ∧ a 1 ∈ Set.range b :=
    both_arc_endpoints_lie_in_other_of_no_cutpoint a b ha hb hmeet (hcut 0) (hcut 1)
  have hA : IsClosed (Set.range a) := (isCompact_range a.continuous).isClosed
  have h0 : a 0 = b 0 ∨ a 0 = b 1 :=
    shared_endpoint_cannot_be_inside_other_arc (Set.range a) b hA hb
      (a 0) (a 1) ha01 ⟨1, rfl⟩ hmeet (hcut 0) hends.1 hends.2
  have h1 : a 1 = b 0 ∨ a 1 = b 1 :=
    shared_endpoint_cannot_be_inside_other_arc (Set.range a) b hA hb
      (a 1) (a 0) ha01.symm ⟨0, rfl⟩
      (by simpa [Set.pair_comm] using hmeet) (hcut 1) hends.2 hends.1
  rcases h0 with h00 | h01
  · rcases h1 with h10 | h11
    · exact False.elim (ha01 (h00.trans h10.symm))
    · exact Or.inl ⟨h00.symm, h11.symm⟩
  · rcases h1 with h10 | h11
    · exact Or.inr ⟨h10.symm, h01.symm⟩
    · exact False.elim (ha01 (h01.trans h11.symm))
