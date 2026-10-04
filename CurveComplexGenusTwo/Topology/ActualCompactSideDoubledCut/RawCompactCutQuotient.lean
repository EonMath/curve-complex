import CurveComplexGenusTwo.Topology.ActualThreeArcCount.FiniteDisjointProperArcStripsNamed

open Set Topology CurveComplex

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

variable {S : Type} [TopologicalSpace S] {n : ℕ}

private abbrev HalfWidth := Set.Icc (0 : ℝ) 1
private abbrev FullWidth := Set.Icc (-1 : ℝ) 1
private abbrev HalfBand := Interval × HalfWidth
private abbrev FullBand := Interval × FullWidth

def bandInterior (E : Fin n → C(FullBand, S)) (i : Fin n) : Set S :=
  E i '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}

def outsideBands (E : Fin n → C(FullBand, S)) : Set S :=
  (⋃ i, bandInterior E i)ᶜ

abbrev RawCut (E : Fin n → C(FullBand, S)) :=
  (outsideBands E) ⊕ (Σ _i : Fin n, Σ _b : Bool, HalfBand)

def signedWidth (b : Bool) (w : HalfWidth) : FullWidth :=
  ⟨if b then (w : ℝ) else -(w : ℝ), by
    cases b <;> dsimp <;>
      constructor <;> nlinarith [w.property.1,w.property.2]⟩

def rawProjection (E : Fin n → C(FullBand, S)) : RawCut E → S
  | Sum.inl z => z.val
  | Sum.inr ⟨i,b,z⟩ => E i (z.1, signedWidth b z.2)

theorem continuous_signedWidth (b : Bool) : Continuous (signedWidth b) := by
  apply Continuous.subtype_mk
  cases b
  · change Continuous (fun w : HalfWidth => -(w : ℝ))
    exact (continuous_subtype_val : Continuous (fun w : HalfWidth => (w : ℝ))).neg
  · change Continuous (fun w : HalfWidth => (w : ℝ))
    exact continuous_subtype_val

theorem signedWidth_injective (b : Bool) : Function.Injective (signedWidth b) := by
  intro u v h
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  cases b
  · dsimp [signedWidth] at hv
    linarith
  · simpa [signedWidth] using hv

theorem signedWidth_opposite_eq_zero {u v : HalfWidth}
    (h : signedWidth false u = signedWidth true v) : (u : ℝ) = 0 := by
  have hv := congrArg Subtype.val h
  dsimp [signedWidth] at hv
  have hu := u.property.1
  have hw := v.property.1
  linarith

theorem halfWidth_zero_of_signedWidth_zero (b : Bool) {w : HalfWidth}
    (h : signedWidth b w = (⟨0,by norm_num⟩ : FullWidth)) :
    w = (⟨0,by norm_num⟩ : HalfWidth) := by
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  cases b <;> dsimp [signedWidth] at hv <;> linarith

theorem exists_signedWidth (w : FullWidth) :
    ∃ b : Bool, ∃ v : HalfWidth, signedWidth b v = w := by
  by_cases h : 0 ≤ (w : ℝ)
  · refine ⟨true, ⟨w.val, h, w.property.2⟩, ?_⟩
    apply Subtype.ext
    simp [signedWidth]
  · refine ⟨false, ⟨-w.val, by constructor <;> linarith [w.property.1]⟩, ?_⟩
    apply Subtype.ext
    simp [signedWidth]

theorem continuous_rawProjection (E : Fin n → C(FullBand, S)) :
    Continuous (rawProjection E) := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_subtype_val
  · apply continuous_sigma
    intro i
    apply continuous_sigma
    intro b
    have hw : Continuous (fun z : HalfBand => signedWidth b z.2) :=
      (continuous_signedWidth b).comp continuous_snd
    have hz : Continuous (fun z : HalfBand => (z.1, signedWidth b z.2)) :=
      continuous_fst.prodMk hw
    exact (E i).continuous.comp hz

def arcCenters (E : Fin n → C(FullBand, S)) : Set S :=
  ⋃ i, Set.range (fun t : Interval => E i (t,⟨0,by norm_num⟩))

theorem center_not_outside (E : Fin n → C(FullBand, S))
    (z : outsideBands E) : z.val ∉ arcCenters E := by
  intro hz
  rcases Set.mem_iUnion.mp hz with ⟨i, t, ht⟩
  have hmem : (E i (t, ⟨0, by norm_num⟩)) ∈ bandInterior E i := by
    exact ⟨(t,⟨0,by norm_num⟩), by norm_num, rfl⟩
  exact z.property (Set.mem_iUnion.mpr ⟨i, by simpa [ht] using hmem⟩)

theorem halfBand_projection_eq_same_index
    (E : Fin n → C(FullBand, S))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    {i j : Fin n} {b c : Bool} {z w : HalfBand}
    (h : E i (z.1, signedWidth b z.2) = E j (w.1, signedWidth c w.2)) :
    i = j := by
  by_contra hij
  have hi : E i (z.1, signedWidth b z.2) ∈ Set.range (E i) :=
    ⟨_, rfl⟩
  have hj : E i (z.1, signedWidth b z.2) ∈ Set.range (E j) :=
    ⟨_, h.symm⟩
  exact Set.disjoint_left.mp (hdisjoint i j hij) hi hj

theorem halfBand_projection_injective_off_centers
    (E : Fin n → C(FullBand, S)) (hemb : ∀ i, Topology.IsEmbedding (E i))
    {i : Fin n} {b c : Bool} {z w : HalfBand}
    (h : E i (z.1, signedWidth b z.2) = E i (w.1, signedWidth c w.2))
    (hoff : E i (z.1, signedWidth b z.2) ∉ arcCenters E) :
    b = c ∧ z = w := by
  have hp := (hemb i).injective h
  have ht : z.1 = w.1 := congrArg (fun q : FullBand => q.1) hp
  have hw : signedWidth b z.2 = signedWidth c w.2 :=
    congrArg (fun q : FullBand => q.2) hp
  cases b <;> cases c
  · exact ⟨rfl, Prod.ext ht ((signedWidth_injective false) hw)⟩
  · have hz : z.2 = (⟨0, by norm_num⟩ : HalfWidth) :=
      Subtype.ext (signedWidth_opposite_eq_zero hw)
    exfalso
    apply hoff
    exact Set.mem_iUnion.mpr ⟨i, ⟨z.1, by simp [hz, signedWidth]⟩⟩
  · have hz : w.2 = (⟨0, by norm_num⟩ : HalfWidth) :=
      Subtype.ext (signedWidth_opposite_eq_zero hw.symm)
    exfalso
    apply hoff
    exact Set.mem_iUnion.mpr ⟨i, ⟨w.1, by simpa [ht, hz, signedWidth] using h.symm⟩⟩
  · exact ⟨rfl, Prod.ext ht ((signedWidth_injective true) hw)⟩

theorem right_projection_injective_off_centers
    (E : Fin n → C(FullBand, S)) (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    {u v : Σ _i : Fin n, Σ _b : Bool, HalfBand}
    (h : rawProjection E (Sum.inr u) = rawProjection E (Sum.inr v))
    (hoff : rawProjection E (Sum.inr u) ∉ arcCenters E) : u = v := by
  rcases u with ⟨i,b,z⟩
  rcases v with ⟨j,c,w⟩
  have hij := halfBand_projection_eq_same_index E hdisjoint h
  subst j
  obtain ⟨hbc,hzw⟩ := halfBand_projection_injective_off_centers E hemb h hoff
  subst c
  subst w
  rfl

def rawRel (E : Fin n → C(FullBand, S)) : RawCut E → RawCut E → Prop :=
  fun u v => u = v ∨
    (rawProjection E u = rawProjection E v ∧
      rawProjection E u ∉ arcCenters E)

theorem rawRel_equivalence (E : Fin n → C(FullBand, S)) :
    Equivalence (rawRel E) := by
  constructor
  · intro u
    exact Or.inl rfl
  · intro u v huv
    rcases huv with h | ⟨hp,ha⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hp.symm, hp ▸ ha⟩
  · intro u v w huv hvw
    rcases huv with h | ⟨hp,ha⟩
    · subst v
      exact hvw
    rcases hvw with h | ⟨hq,_⟩
    · subst w
      exact Or.inr ⟨hp,ha⟩
    · exact Or.inr ⟨hp.trans hq,ha⟩

def rawSetoid (E : Fin n → C(FullBand, S)) : Setoid (RawCut E) :=
  ⟨rawRel E, rawRel_equivalence E⟩

def mixedPair (E : Fin n → C(FullBand, S)) : Set (RawCut E × RawCut E) :=
  (Set.range (Sum.inl : outsideBands E → RawCut E) ×ˢ
      Set.range (Sum.inr : (Σ _i : Fin n, Σ _b : Bool, HalfBand) → RawCut E)) ∪
  (Set.range (Sum.inr : (Σ _i : Fin n, Σ _b : Bool, HalfBand) → RawCut E) ×ˢ
      Set.range (Sum.inl : outsideBands E → RawCut E))

theorem rawRel_iff_closed_formula (E : Fin n → C(FullBand, S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (u v : RawCut E) :
    rawRel E u v ↔ u = v ∨
      (rawProjection E u = rawProjection E v ∧ (u,v) ∈ mixedPair E) := by
  constructor
  · intro huv
    rcases huv with h | ⟨h,hoff⟩
    · exact Or.inl h
    rcases u with x | x <;> rcases v with y | y
    · left
      exact congrArg Sum.inl (Subtype.ext h)
    · right
      exact ⟨h, Or.inl ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩⟩
    · right
      exact ⟨h, Or.inr ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩⟩
    · left
      exact congrArg Sum.inr (right_projection_injective_off_centers E hemb hdisjoint h hoff)
  · intro huv
    rcases huv with h | ⟨h,hm⟩
    · exact Or.inl h
    rcases hm with ⟨⟨x,hx⟩,⟨y,hy⟩⟩ | ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    · change Sum.inl x = u at hx
      change Sum.inr y = v at hy
      subst u
      exact Or.inr ⟨h, center_not_outside E x⟩
    · change Sum.inr x = u at hx
      change Sum.inl y = v at hy
      subst v
      change rawProjection E u = y.val at h
      exact Or.inr ⟨h, by
        intro hc
        exact center_not_outside E y (h ▸ hc)⟩

theorem rawRel_isClosed [T2Space S]
    (E : Fin n → C(FullBand, S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j))) :
    IsClosed {p : RawCut E × RawCut E | rawRel E p.1 p.2} := by
  have hleft : IsClosed (Set.range (Sum.inl : outsideBands E → RawCut E)) :=
    isClosed_range_inl
  have hright : IsClosed
      (Set.range (Sum.inr : (Σ _i : Fin n, Σ _b : Bool, HalfBand) → RawCut E)) :=
    isClosed_range_inr
  have hmixed : IsClosed (mixedPair E) :=
    (hleft.prod hright).union (hright.prod hleft)
  have hdiag : IsClosed {p : RawCut E × RawCut E | p.1 = p.2} :=
    isClosed_eq continuous_fst continuous_snd
  have hproj : IsClosed {p : RawCut E × RawCut E |
      rawProjection E p.1 = rawProjection E p.2} :=
    isClosed_eq ((continuous_rawProjection E).comp continuous_fst)
      ((continuous_rawProjection E).comp continuous_snd)
  convert hdiag.union (hproj.inter hmixed) using 1
  ext p
  exact rawRel_iff_closed_formula E hemb hdisjoint p.1 p.2

abbrev CutQuotient (E : Fin n → C(FullBand, S)) := Quotient (rawSetoid E)

def cutProjection (E : Fin n → C(FullBand, S)) : CutQuotient E → S :=
  Quotient.lift (rawProjection E) (by
    intro u v huv
    rcases huv with h | ⟨h,_⟩
    · exact congrArg (rawProjection E) h
    · exact h)

theorem continuous_cutProjection (E : Fin n → C(FullBand, S)) :
    Continuous (cutProjection E) :=
  (continuous_rawProjection E).quotient_lift _

def cutSide (E : Fin n → C(FullBand, S)) (i : Fin n) (b : Bool) :
    C(Interval, CutQuotient E) where
  toFun t := Quotient.mk (rawSetoid E)
    (Sum.inr ⟨i,b,(t,⟨0,by norm_num⟩)⟩)
  continuous_toFun := by
    apply continuous_quotient_mk'.comp
    exact continuous_inr.comp (continuous_sigmaMk.comp
      (continuous_sigmaMk.comp (continuous_id.prodMk continuous_const)))

theorem cutSide_projection (E : Fin n → C(FullBand, S))
    (i : Fin n) (b : Bool) (t : Interval) :
    cutProjection E (cutSide E i b t) =
      E i (t,⟨0,by norm_num⟩) := by
  cases b <;> simp [cutProjection, cutSide, rawProjection, signedWidth]

theorem cutSide_distinct (E : Fin n → C(FullBand, S))
    (i : Fin n) (t : Interval) : cutSide E i false t ≠ cutSide E i true t := by
  intro h
  have hr := Quotient.exact h
  rcases hr with heq | ⟨_,hoff⟩
  · simp at heq
  · apply hoff
    exact Set.mem_iUnion.mpr ⟨i, ⟨t, by
      simp [rawProjection, signedWidth]⟩⟩

theorem cut_arc_center_fiber
    (E : Fin n → C(FullBand, S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (i : Fin n) (t : Interval) :
    {q : CutQuotient E | cutProjection E q = E i (t,⟨0,by norm_num⟩)} =
      {cutSide E i false t, cutSide E i true t} := by
  ext q
  constructor
  · intro hq
    induction q using Quotient.ind with
    | _ r =>
      rcases r with z | ⟨j,b,z⟩
      · have hc : z.val ∈ arcCenters E :=
          Set.mem_iUnion.mpr ⟨i, ⟨t, by simpa [cutProjection, rawProjection] using hq.symm⟩⟩
        exact False.elim ((center_not_outside E z) hc)
      · have hp : E j (z.1, signedWidth b z.2) =
            E i (t, signedWidth false (⟨0,by norm_num⟩ : HalfWidth)) := by
          simpa [cutProjection, rawProjection, signedWidth] using hq
        have hij := halfBand_projection_eq_same_index E hdisjoint
          (i := j) (j := i) (b := b) (c := false)
          (z := z) (w := (t,⟨0,by norm_num⟩)) hp
        subst j
        have hp' : (z.1, signedWidth b z.2) =
            (t, signedWidth false (⟨0,by norm_num⟩ : HalfWidth)) :=
          (hemb i).injective hp
        have ht : z.1 = t := congrArg (fun p : FullBand => p.1) hp'
        have hw : z.2 = (⟨0,by norm_num⟩ : HalfWidth) :=
          halfWidth_zero_of_signedWidth_zero b (by
            simpa [signedWidth] using congrArg (fun p : FullBand => p.2) hp')
        have hz : z = (t, (⟨0,by norm_num⟩ : HalfWidth)) := Prod.ext ht hw
        cases b <;> simp [cutSide, hz]
  · intro hq
    rcases Set.mem_insert_iff.mp hq with h | h
    · simpa [h] using cutSide_projection E i false t
    · have h := Set.mem_singleton_iff.mp h
      simpa [h] using cutSide_projection E i true t

theorem rawProjection_surjective (E : Fin n → C(FullBand, S)) :
    Function.Surjective (rawProjection E) := by
  intro s
  by_cases h : s ∈ ⋃ i, bandInterior E i
  · rcases Set.mem_iUnion.mp h with ⟨i, z, _, hz⟩
    rcases exists_signedWidth z.2 with ⟨b,v,hv⟩
    refine ⟨Sum.inr ⟨i,b,(z.1,v)⟩, ?_⟩
    simpa [rawProjection, hv] using hz
  · exact ⟨Sum.inl ⟨s,h⟩, rfl⟩

theorem cutProjection_surjective (E : Fin n → C(FullBand, S)) :
    Function.Surjective (cutProjection E) := by
  intro s
  obtain ⟨r,hr⟩ := rawProjection_surjective E s
  exact ⟨Quotient.mk (rawSetoid E) r, hr⟩

theorem cutProjection_injective_off_centers
    (E : Fin n → C(FullBand, S))
    {u v : CutQuotient E}
    (h : cutProjection E u = cutProjection E v)
    (hoff : cutProjection E u ∉ arcCenters E) : u = v := by
  induction u using Quotient.ind with
  | _ x =>
    induction v using Quotient.ind with
    | _ y =>
      exact (Quotient.eq).mpr (Or.inr ⟨h, hoff⟩)

section Compactness

variable [T2Space S] [CompactSpace S]

theorem rawCut_compact (E : Fin n → C(FullBand, S))
    (hopen : ∀ i, IsOpen (bandInterior E i)) : CompactSpace (RawCut E) := by
  have hclosed : IsClosed (outsideBands E) := by
    unfold outsideBands
    exact (isOpen_iUnion hopen).isClosed_compl
  letI : CompactSpace (outsideBands E) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  infer_instance

theorem cutQuotient_compact (E : Fin n → C(FullBand, S))
    (hopen : ∀ i, IsOpen (bandInterior E i)) : CompactSpace (CutQuotient E) := by
  letI := rawCut_compact E hopen
  infer_instance

theorem quotient_mk_isClosedMap (E : Fin n → C(FullBand, S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j))) :
    IsClosedMap (Quotient.mk (rawSetoid E) : RawCut E → CutQuotient E) := by
  letI := rawCut_compact E hopen
  intro A hA
  have hgraph : IsClosed {p : RawCut E × RawCut E |
      p.1 ∈ A ∧ rawRel E p.1 p.2} :=
    (hA.preimage continuous_fst).inter (rawRel_isClosed E hemb hdisjoint)
  have hsat : IsClosed (Prod.snd '' {p : RawCut E × RawCut E |
      p.1 ∈ A ∧ rawRel E p.1 p.2}) :=
    (hgraph.isCompact.image continuous_snd).isClosed
  apply isClosed_coinduced.mpr
  convert hsat using 1
  ext v
  constructor
  · rintro ⟨u,hu,hq⟩
    exact ⟨(u,v), ⟨hu, (Quotient.eq).mp hq⟩, rfl⟩
  · rintro ⟨⟨u,w⟩, ⟨hu,hr⟩, hw⟩
    change w = v at hw
    subst w
    exact ⟨u, hu, (Quotient.eq).mpr hr⟩

theorem quotient_mk_isProperMap (E : Fin n → C(FullBand, S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j))) :
    IsProperMap (Quotient.mk (rawSetoid E) : RawCut E → CutQuotient E) := by
  letI := rawCut_compact E hopen
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨continuous_quotient_mk', quotient_mk_isClosedMap E hopen hemb hdisjoint, ?_⟩
  intro y
  induction y using Quotient.ind with
  | _ u =>
    have hclass : IsClosed {v : RawCut E | rawRel E v u} := by
      have h := rawRel_isClosed E hemb hdisjoint
      exact h.preimage (continuous_id.prodMk continuous_const)
    convert hclass.isCompact using 1
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact Quotient.eq

theorem cutQuotient_hausdorff (E : Fin n → C(FullBand, S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j))) :
    T2Space (CutQuotient E) := by
  letI := rawCut_compact E hopen
  let f : RawCut E → CutQuotient E := Quotient.mk (rawSetoid E)
  have hf : IsProperMap f := quotient_mk_isProperMap E hopen hemb hdisjoint
  have hpair : IsProperMap (Prod.map f f) := hf.prodMap hf
  have hsurj : Function.Surjective (Prod.map f f) := by
    intro ⟨u,v⟩
    induction u using Quotient.ind with
    | _ x =>
      induction v using Quotient.ind with
      | _ y => exact ⟨(x,y), rfl⟩
  have hquot : IsQuotientMap (Prod.map f f) :=
    hpair.isClosedMap.isQuotientMap hpair.continuous hsurj
  apply t2_iff_isClosed_diagonal.mpr
  apply (isQuotientMap_iff_isClosed.mp hquot).2 (diagonal (CutQuotient E)) |>.mpr
  convert rawRel_isClosed E hemb hdisjoint using 1
  ext p
  change (Quotient.mk (rawSetoid E) p.1 = Quotient.mk (rawSetoid E) p.2) ↔
    rawRel E p.1 p.2
  exact Quotient.eq

theorem arcCenters_isClosed (E : Fin n → C(FullBand, S)) :
    IsClosed (arcCenters E) := by
  unfold arcCenters
  apply isClosed_iUnion_of_finite
  intro i
  exact (isCompact_range ((E i).continuous.comp
    (continuous_id.prodMk continuous_const))).isClosed

def cutCore (E : Fin n → C(FullBand, S)) : Set (CutQuotient E) :=
  cutProjection E ⁻¹' (arcCenters E)ᶜ

theorem cutCore_isOpen (E : Fin n → C(FullBand, S)) :
    IsOpen (cutCore E) :=
  (arcCenters_isClosed E).isOpen_compl.preimage (continuous_cutProjection E)

noncomputable def cutCoreHomeomorph (E : Fin n → C(FullBand, S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j))) :
    ↥(cutCore E) ≃ₜ ↥(arcCenters E)ᶜ := by
  letI := cutQuotient_compact E hopen
  let f := ((arcCenters E)ᶜ).restrictPreimage (cutProjection E)
  have hbij : Function.Bijective f := by
    constructor
    · intro u v h
      apply Subtype.ext
      exact cutProjection_injective_off_centers E
        (congrArg Subtype.val h) u.property
    · intro y
      obtain ⟨q,hq⟩ := cutProjection_surjective E y.val
      refine ⟨⟨q, ?_⟩, ?_⟩
      · change cutProjection E q ∈ (arcCenters E)ᶜ
        simpa [hq] using y.property
      · apply Subtype.ext
        exact hq
  exact (Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed
    ((continuous_cutProjection E).restrictPreimage)
    ((continuous_cutProjection E).isClosedMap.restrictPreimage _)

def cutInteriorCore (E : Fin n → C(FullBand, S)) (B : Set S) :
    Set (CutQuotient E) :=
  cutProjection E ⁻¹' (B ∪ arcCenters E)ᶜ

theorem cutInteriorCore_isOpen (E : Fin n → C(FullBand, S))
    (B : Set S) (hB : IsClosed B) : IsOpen (cutInteriorCore E B) := by
  exact (hB.union (arcCenters_isClosed E)).isOpen_compl.preimage
    (continuous_cutProjection E)

noncomputable def cutInteriorCoreHomeomorph (E : Fin n → C(FullBand, S))
    (B : Set S)
    (hopen : ∀ i, IsOpen (bandInterior E i)) :
    ↥(cutInteriorCore E B) ≃ₜ ↥(B ∪ arcCenters E)ᶜ := by
  letI := cutQuotient_compact E hopen
  let f := ((B ∪ arcCenters E)ᶜ).restrictPreimage (cutProjection E)
  have hbij : Function.Bijective f := by
    constructor
    · intro u v h
      apply Subtype.ext
      apply cutProjection_injective_off_centers E (congrArg Subtype.val h)
      exact fun hc => u.property (Or.inr hc)
    · intro y
      obtain ⟨q,hq⟩ := cutProjection_surjective E y.val
      refine ⟨⟨q, ?_⟩, ?_⟩
      · change cutProjection E q ∈ (B ∪ arcCenters E)ᶜ
        simpa [hq] using y.property
      · exact Subtype.ext hq
  exact (Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed
    ((continuous_cutProjection E).restrictPreimage)
    ((continuous_cutProjection E).isClosedMap.restrictPreimage _)

def cutBaseBoundary (E : Fin n → C(FullBand, S)) (B : Set S) :
    Set (CutQuotient E) := cutProjection E ⁻¹' B

theorem cutBaseBoundary_image (E : Fin n → C(FullBand, S)) (B : Set S) :
    Set.range (fun z : ↥(cutBaseBoundary E B) => cutProjection E z.val) = B := by
  ext s
  constructor
  · rintro ⟨z,rfl⟩
    exact z.property
  · intro hs
    obtain ⟨q,hq⟩ := cutProjection_surjective E s
    exact ⟨⟨q, by change cutProjection E q ∈ B; exact hq.symm ▸ hs⟩, hq⟩

theorem cutInteriorCore_boundary_exhaustion
    (E : Fin n → C(FullBand, S)) (B : Set S)
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j))) :
    (cutInteriorCore E B)ᶜ = cutBaseBoundary E B ∪
      ⋃ i, (Set.range (cutSide E i false) ∪ Set.range (cutSide E i true)) := by
  ext q
  constructor
  · intro hq
    simp only [cutInteriorCore, Set.mem_compl_iff, Set.mem_preimage, not_not] at hq
    rcases hq with hB | hA
    · exact Or.inl hB
    · rcases Set.mem_iUnion.mp hA with ⟨i, t, ht⟩
      have hf : q ∈ {z : CutQuotient E |
          cutProjection E z = E i (t,⟨0,by norm_num⟩)} := ht.symm
      rw [cut_arc_center_fiber E hemb hdisjoint i t] at hf
      rcases Set.mem_insert_iff.mp hf with hf | hf
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inl ⟨t,hf.symm⟩⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inr ⟨t,
          (Set.mem_singleton_iff.mp hf).symm⟩⟩)
  · intro hq
    simp only [cutInteriorCore, Set.mem_compl_iff, Set.mem_preimage, not_not]
    rcases hq with hB | hside
    · exact Or.inl hB
    · rcases Set.mem_iUnion.mp hside with ⟨i, hfalse | htrue⟩
      · rcases hfalse with ⟨t,rfl⟩
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨t,
          (cutSide_projection E i false t).symm⟩⟩)
      · rcases htrue with ⟨t,rfl⟩
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨t,
          (cutSide_projection E i true t).symm⟩⟩)

theorem cutSide_not_core (E : Fin n → C(FullBand, S)) (B : Set S)
    (i : Fin n) (b : Bool) (t : Interval) :
    cutSide E i b t ∈ (cutInteriorCore E B)ᶜ := by
  simp only [cutInteriorCore, Set.mem_compl_iff, Set.mem_preimage, not_not]
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨t,
    (cutSide_projection E i b t).symm⟩⟩)

theorem cutSide_endpoint_incidence (E : Fin n → C(FullBand, S))
    (B : Set S) (i : Fin n) (b : Bool)
    (hstart : E i (0,⟨0,by norm_num⟩) ∈ B)
    (hend : E i (1,⟨0,by norm_num⟩) ∈ B) :
    cutSide E i b 0 ∈ cutBaseBoundary E B ∧
      cutSide E i b 1 ∈ cutBaseBoundary E B := by
  constructor
  · change cutProjection E (cutSide E i b 0) ∈ B
    simpa [cutSide_projection] using hstart
  · change cutProjection E (cutSide E i b 1) ∈ B
    simpa [cutSide_projection] using hend

theorem cutBaseBoundary_regular_fiber
    (E : Fin n → C(FullBand, S)) (B : Set S)
    (hBcenters : ∀ i t, E i (t,⟨0,by norm_num⟩) ∈ B → t = 0 ∨ t = 1)
    (y : S) (hy : y ∈ B)
    (hregular : ∀ i, y ≠ E i (0,⟨0,by norm_num⟩) ∧
      y ≠ E i (1,⟨0,by norm_num⟩)) :
    ∃! q : CutQuotient E, q ∈ cutBaseBoundary E B ∧ cutProjection E q = y := by
  obtain ⟨q,hq⟩ := cutProjection_surjective E y
  refine ⟨q, ⟨by change cutProjection E q ∈ B; exact hq.symm ▸ hy, hq⟩, ?_⟩
  intro z hz
  have hoff : y ∉ arcCenters E := by
    intro hc
    rcases Set.mem_iUnion.mp hc with ⟨i,t,ht⟩
    have hBt : E i (t,⟨0,by norm_num⟩) ∈ B := by
      simpa [ht] using hy
    rcases hBcenters i t hBt with h0 | h1
    · exact (hregular i).1 (by simpa [h0] using ht.symm)
    · exact (hregular i).2 (by simpa [h1] using ht.symm)
  exact cutProjection_injective_off_centers E (hz.2.trans hq.symm)
    (hz.2 ▸ hoff)

end Compactness

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
