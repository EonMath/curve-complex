import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalEndpointFixedPushOff

open CurveComplex Set Topology

namespace RegionalEmbeddedFamily

private def firstClock (t : Interval) : Interval :=
  ⟨min 1 (2 * (t : ℝ)), by
    constructor
    · exact le_min (by norm_num) (by nlinarith [t.property.1])
    · exact min_le_left _ _⟩

private def secondClock (t : Interval) : Interval :=
  ⟨max 0 (2 * (t : ℝ) - 1), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (by nlinarith [t.property.2])⟩

private noncomputable def halfInterval : Interval := ⟨1 / 2, by norm_num⟩

private theorem firstClock_continuous : Continuous firstClock := by
  apply Continuous.subtype_mk
  fun_prop

private theorem secondClock_continuous : Continuous secondClock := by
  apply Continuous.subtype_mk
  fun_prop

private theorem firstClock_zero : firstClock 0 = 0 := Subtype.ext (by norm_num [firstClock])
private theorem firstClock_half : firstClock halfInterval = 1 :=
  Subtype.ext (by norm_num [firstClock, halfInterval])
private theorem secondClock_half : secondClock halfInterval = 0 :=
  Subtype.ext (by norm_num [secondClock, halfInterval])
private theorem secondClock_one : secondClock 1 = 1 :=
  Subtype.ext (by norm_num [secondClock])

theorem compose_regional_embedded_families
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b c : C(Interval, ↥F))
    (U V : C(Interval × Interval, ↥F))
    (ρ σ : Interval ≃ₜ Interval)
    (hρ0 : ρ 0 = 0) (hρ1 : ρ 1 = 1)
    (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 1)
    (hU0 : ∀ s, U (0,s) = a s)
    (hU1 : ∀ s, U (1,s) = b (ρ s))
    (hV0 : ∀ s, V (0,s) = b s)
    (hV1 : ∀ s, V (1,s) = c (σ s))
    (hUemb : ∀ t, Topology.IsEmbedding (fun s => U (t,s)))
    (hVemb : ∀ t, Topology.IsEmbedding (fun s => V (t,s)))
    (hUends : ∀ t, U (t,0) = a 0 ∧ U (t,1) = a 1)
    (hVends : ∀ t, V (t,0) = b 0 ∧ V (t,1) = b 1)
    (hUclear : ∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
      (U (t,s)).val ∉ frontier F)
    (hVclear : ∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
      (V (t,s)).val ∉ frontier F) :
    ∃ (W : C(Interval × Interval, ↥F)) (τ : Interval ≃ₜ Interval),
      τ 0 = 0 ∧ τ 1 = 1 ∧
      (∀ s, W (0,s) = a s) ∧
      (∀ s, W (1,s) = c (τ s)) ∧
      (∀ t, Topology.IsEmbedding (fun s => W (t,s))) ∧
      (∀ t, W (t,0) = a 0 ∧ W (t,1) = a 1) ∧
      (∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
        (W (t,s)).val ∉ frontier F) := by
  let A : C(Interval × Interval, ↥F) :=
    ⟨fun p => U (firstClock p.1,p.2),
      U.continuous.comp ((firstClock_continuous.comp continuous_fst).prodMk
        continuous_snd)⟩
  let B : C(Interval × Interval, ↥F) :=
    ⟨fun p => V (secondClock p.1,ρ p.2),
      V.continuous.comp ((secondClock_continuous.comp continuous_fst).prodMk
        (ρ.continuous.comp continuous_snd))⟩
  let L : Set (Interval × Interval) :=
    {p | (p.1 : ℝ) ≤ 1 / 2}
  have hseam (p : Interval × Interval) (hp : (p.1 : ℝ) = 1 / 2) :
      A p = B p := by
    have hp' : p.1 = halfInterval := Subtype.ext hp
    change U (firstClock p.1,p.2) = V (secondClock p.1,ρ p.2)
    rw [hp', firstClock_half, secondClock_half, hU1, hV0]
  have hcont : Continuous (L.piecewise A B) := by
    apply Continuous.piecewise _ A.continuous B.continuous
    intro p hp
    have he := frontier_le_subset_eq
      (continuous_subtype_val.comp continuous_fst) continuous_const hp
    exact hseam p he
  let W : C(Interval × Interval, ↥F) :=
    ⟨L.piecewise A B, hcont⟩
  let τ : Interval ≃ₜ Interval := ρ.trans σ
  have hτ0 : τ 0 = 0 := by simp [τ, hρ0, hσ0]
  have hτ1 : τ 1 = 1 := by simp [τ, hρ1, hσ1]
  have hρinterior (s : Interval) (hs : s ∈ Set.Ioo (0 : Interval) 1) :
      ρ s ∈ Set.Ioo (0 : Interval) 1 := by
    have hn0 : ρ s ≠ 0 := by
      intro he
      exact ne_of_gt hs.1 (ρ.injective (he.trans hρ0.symm))
    have hn1 : ρ s ≠ 1 := by
      intro he
      exact ne_of_lt hs.2 (ρ.injective (he.trans hρ1.symm))
    exact ⟨lt_of_le_of_ne (ρ s).property.1 (Ne.symm hn0),
      lt_of_le_of_ne (ρ s).property.2 hn1⟩
  refine ⟨W, τ, hτ0, hτ1, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    have hL : (0,s) ∈ L := by change (0 : ℝ) ≤ 1 / 2; norm_num
    change L.piecewise A B (0,s) = a s
    rw [Set.piecewise_eq_of_mem L A B hL]
    change U (firstClock 0,s) = a s
    rw [firstClock_zero]
    exact hU0 s
  · intro s
    have hL : (1,s) ∉ L := by change ¬(1 : ℝ) ≤ 1 / 2; norm_num
    change L.piecewise A B (1,s) = c (τ s)
    rw [Set.piecewise_eq_of_notMem L A B hL]
    change V (secondClock 1,ρ s) = c (τ s)
    rw [secondClock_one]
    exact hV1 (ρ s)
  · intro t
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · have he : (fun s : Interval => W (t,s)) =
          (fun s => U (firstClock t,s)) := by
        funext s
        exact Set.piecewise_eq_of_mem L A B ht
      rw [he]
      exact hUemb (firstClock t)
    · have he : (fun s : Interval => W (t,s)) =
          (fun s => V (secondClock t,ρ s)) := by
        funext s
        exact Set.piecewise_eq_of_notMem L A B ht
      rw [he]
      exact (hVemb (secondClock t)).comp ρ.isEmbedding
  · intro t
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · constructor
      · change L.piecewise A B (t,0) = a 0
        rw [Set.piecewise_eq_of_mem L A B (show (t,0) ∈ L from ht)]
        exact (hUends (firstClock t)).1
      · change L.piecewise A B (t,1) = a 1
        rw [Set.piecewise_eq_of_mem L A B (show (t,1) ∈ L from ht)]
        exact (hUends (firstClock t)).2
    · have hL0 : (t,0) ∉ L := ht
      have hL1 : (t,1) ∉ L := ht
      have hEnds := hVends (secondClock t)
      have hb0 : b 0 = a 0 := by
        calc b 0 = b (ρ 0) := by rw [hρ0]
          _ = U (1,0) := (hU1 0).symm
          _ = a 0 := (hUends 1).1
      have hb1 : b 1 = a 1 := by
        calc b 1 = b (ρ 1) := by rw [hρ1]
          _ = U (1,1) := (hU1 1).symm
          _ = a 1 := (hUends 1).2
      constructor
      · change L.piecewise A B (t,0) = a 0
        rw [Set.piecewise_eq_of_notMem L A B hL0]
        change V (secondClock t,ρ 0) = a 0
        rw [hρ0]
        exact hEnds.1.trans hb0
      · change L.piecewise A B (t,1) = a 1
        rw [Set.piecewise_eq_of_notMem L A B hL1]
        change V (secondClock t,ρ 1) = a 1
        rw [hρ1]
        exact hEnds.2.trans hb1
  · intro t s hs
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · change (L.piecewise A B (t,s)).val ∉ frontier F
      rw [Set.piecewise_eq_of_mem L A B ht]
      exact hUclear (firstClock t) s hs
    · change (L.piecewise A B (t,s)).val ∉ frontier F
      rw [Set.piecewise_eq_of_notMem L A B ht]
      exact hVclear (secondClock t) (ρ s) (hρinterior s hs)

end RegionalEmbeddedFamily
