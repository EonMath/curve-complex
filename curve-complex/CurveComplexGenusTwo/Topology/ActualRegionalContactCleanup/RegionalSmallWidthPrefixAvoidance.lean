import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalSmallWidthAmbientMove
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalStripPrefixLocalization

open CurveComplex Set Topology

theorem regional_strip_local_side_gives_global_ambient_copy
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBFront : B ⊆ frontier F)
    (a : C(Interval,↥F))
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = a t)
    (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
    (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
      (E (t,w)).val ∈ interior F)
    (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (K : Set ↥F) (hK : IsClosed K)
    (V : Set Interval) (hV : IsOpen V)
    (hfar : ∀ t ∈ Vᶜ, a t ∉ K)
    (η : ℝ) (hη : 0 < η)
    (hnear : ∀ t ∈ V, ∀ w : Set.Icc (-1 : ℝ) 1,
      0 < (w : ℝ) → (w : ℝ) < η → E (t,w) ∉ K) :
    ∃ (ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1),
      ∃ b : C(Interval,↥F),
        Topology.IsEmbedding b ∧
        (b 0).val ∈ B ∧ (b 1).val ∈ B ∧
        (∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F) ∧
        Disjoint (Set.range b) (Set.range a) ∧
        Disjoint (Set.range b) K ∧
        ∃ H : AmbientIsotopy ↥F,
          (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ B} =
            {y : ↥F | y.val ∈ B}) ∧
          (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
            {y : ↥F | y.val ∈ frontier F}) ∧
          H.finalMap '' Set.range a = Set.range b ∧
          (∀ t y, y ∉ Set.range E → H.map (t,y) = y) := by
  obtain ⟨δ,hδ,hδclear⟩ := regional_strip_compact_prefix_localization
    E K hK V hV (by intro t ht; rw [hcenter]; exact hfar t ht)
  let ε : ℝ := min δ (min η 1) / 2
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ (min η 1)]
  have hεη : ε < η := by
    dsimp [ε]
    linarith [min_le_right δ (min η 1), min_le_left η 1]
  have hε1 : ε < 1 := by
    dsimp [ε]
    linarith [min_le_right δ (min η 1), min_le_right η 1]
  let w : Set.Icc (-1 : ℝ) 1 := ⟨ε,⟨by linarith,by linarith⟩⟩
  let b : C(Interval,↥F) :=
    ⟨fun t => E (t,w), E.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hb : Topology.IsEmbedding b :=
    (b.continuous.isClosedEmbedding (by
      intro t u he
      exact congrArg Prod.fst (hE.injective he))).isEmbedding
  have hba : Disjoint (Set.range b) (Set.range a) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t,rfl⟩ ⟨u,hu⟩
    have he : E (u,⟨0,by norm_num⟩) = E (t,w) := (hcenter u).trans hu
    have hw := congrArg (fun z : Interval × Set.Icc (-1 : ℝ) 1 => (z.2 : ℝ))
      (hE.injective he)
    change (0 : ℝ) = ε at hw
    linarith
  have hbK : Disjoint (Set.range b) K := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t,rfl⟩ hy
    by_cases ht : t ∈ V
    · exact (hnear t ht w hε0 hεη) hy
    · have htw : |(w : ℝ)| < δ := by
        change |ε| < δ
        rw [abs_of_pos hε0]
        exact hεδ
      exact (hδclear t w (Set.mem_compl ht) htw) hy
  obtain ⟨H,hHB,hHF,hmove,hout⟩ :=
    regional_proper_strip_small_width_ambient_move F B hF hBFront E
      hE hend hint hopen ε hε0 hε1
  have hRA : Set.range a =
      Set.range (fun t : Interval => E (t,⟨0,by norm_num⟩)) := by
    congr 1
    funext t
    exact (hcenter t).symm
  refine ⟨ε,hε0,hε1,b,hb,(hend w).1,(hend w).2,?_,hba,hbK,
    H,hHB,hHF,?_,hout⟩
  · intro t ht
    exact (mem_interior_iff_notMem_frontier (b t).property).mp (hint t ht w)
  · rw [hRA]
    exact hmove

#print axioms regional_strip_local_side_gives_global_ambient_copy
