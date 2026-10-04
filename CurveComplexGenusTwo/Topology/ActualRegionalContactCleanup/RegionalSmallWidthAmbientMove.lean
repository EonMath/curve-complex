import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalBandTranslation

open CurveComplex Set Topology

theorem regional_proper_strip_small_width_ambient_move
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBFront : B ⊆ frontier F)
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∈ interior F)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ H : AmbientIsotopy ↥F,
      (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ B} =
        {y : ↥F | y.val ∈ B}) ∧
      (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
        {y : ↥F | y.val ∈ frontier F}) ∧
      H.finalMap '' Set.range (fun t : Interval => E (t,⟨0,by norm_num⟩)) =
        Set.range (fun t : Interval => E (t,⟨ε,⟨by linarith,by linarith⟩⟩)) ∧
      ∀ t y, y ∉ Set.range E → H.map (t,y) = y := by
  let : CompactSpace ↥F := isCompact_iff_compactSpace.mp hF
  obtain ⟨H,hband,houtside⟩ :=
    regional_closed_band_transverse_translation_ambient_isotopy
      E hE hopen ε hε0.le hε1
  have hEboundary (z : Interval × Set.Icc (-1 : ℝ) 1) :
      (E z).val ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
    constructor
    · intro hz
      by_cases h0 : z.1 = 0
      · exact Or.inl h0
      · by_cases h1 : z.1 = 1
        · exact Or.inr h1
        · have ht : z.1 ∈ Set.Ioo (0 : Interval) 1 :=
            ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩
          exact False.elim
            ((mem_interior_iff_notMem_frontier
              (interior_subset (hint z.1 ht z.2))).mp (hint z.1 ht z.2)
                (hBFront hz))
    · rintro (h0 | h1)
      · have hz : z = (0,z.2) := Prod.ext h0 rfl
        rw [hz]
        exact (hend z.2).1
      · have hz : z = (1,z.2) := Prod.ext h1 rfl
        rw [hz]
        exact (hend z.2).2
  have hEfront (z : Interval × Set.Icc (-1 : ℝ) 1) :
      (E z).val ∈ frontier F ↔ z.1 = 0 ∨ z.1 = 1 := by
    constructor
    · intro hz
      by_cases h0 : z.1 = 0
      · exact Or.inl h0
      · by_cases h1 : z.1 = 1
        · exact Or.inr h1
        · have ht : z.1 ∈ Set.Ioo (0 : Interval) 1 :=
            ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩
          exact False.elim
            ((mem_interior_iff_notMem_frontier
              (interior_subset (hint z.1 ht z.2))).mp (hint z.1 ht z.2) hz)
    · intro hz
      exact hBFront ((hEboundary z).mpr hz)
  have hpreserve (D : Set S)
      (hD : ∀ z : Interval × Set.Icc (-1 : ℝ) 1,
        (E z).val ∈ D ↔ z.1 = 0 ∨ z.1 = 1)
      (t : Interval) (y : ↥F) :
      (H.map (t,y)).val ∈ D ↔ y.val ∈ D := by
    by_cases hy : y ∈ Set.range E
    · obtain ⟨z,rfl⟩ := hy
      obtain ⟨w,hw,hHz⟩ := hband t z
      rw [hHz,hD (z.1,w),hD z]
    · rw [houtside t y hy]
  have himage (D : Set S)
      (hD : ∀ z : Interval × Set.Icc (-1 : ℝ) 1,
        (E z).val ∈ D ↔ z.1 = 0 ∨ z.1 = 1)
      (t : Interval) :
      (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ D} =
        {y : ↥F | y.val ∈ D} := by
    apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      exact (hpreserve D hD t z).mpr hz
    · intro y hy
      obtain ⟨h,hh⟩ := H.homeomorphism_at t
      have he : H.map (t,h.symm y) = y :=
        (hh _).symm.trans (h.apply_symm_apply y)
      exact ⟨h.symm y,
        (hpreserve D hD t (h.symm y)).mp (he.symm ▸ hy),he⟩
  refine ⟨H,fun t => himage B hEboundary t,
    fun t => himage (frontier F) hEfront t,?_,houtside⟩
  change (fun y => H.map (1,y)) ''
    Set.range (fun t : Interval => E (t,⟨0,by norm_num⟩)) =
      Set.range (fun t : Interval => E (t,⟨ε,⟨by linarith,by linarith⟩⟩))
  ext y
  constructor
  · rintro ⟨z,⟨t,rfl⟩,rfl⟩
    obtain ⟨w,hw,hHw⟩ := hband 1 (t,⟨0,by norm_num⟩)
    have hwidth : w = ⟨ε,⟨by linarith,by linarith⟩⟩ := by
      apply Subtype.ext
      simpa using hw
    rw [hwidth] at hHw
    exact ⟨t,hHw.symm⟩
  · rintro ⟨t,rfl⟩
    refine ⟨E (t,⟨0,by norm_num⟩),⟨t,rfl⟩,?_⟩
    obtain ⟨w,hw,hHw⟩ := hband 1 (t,⟨0,by norm_num⟩)
    have hwidth : w = ⟨ε,⟨by linarith,by linarith⟩⟩ := by
      apply Subtype.ext
      simpa using hw
    simpa [hwidth] using hHw

#print axioms regional_proper_strip_small_width_ambient_move
