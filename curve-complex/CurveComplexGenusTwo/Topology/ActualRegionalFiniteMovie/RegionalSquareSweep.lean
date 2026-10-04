import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalDiskContainment
import CurveComplexGenusTwo.Topology.ArcStraightening

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

private def squareUpper (s : Interval) : Plane :=
  Plane.mk (max (-1) (1 - 4 * (s : ℝ))) (min 1 (3 - 4 * (s : ℝ)))

private def squareLower (s : Interval) : Plane :=
  Plane.mk (min 1 (3 - 4 * (s : ℝ))) (max (-1) (1 - 4 * (s : ℝ)))

private def squareSweep (t s : Interval) : Plane :=
  (1 - (t : ℝ)) • squareUpper s + (t : ℝ) • squareLower s

private theorem squareUpper_continuous : Continuous squareUpper := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> change Continuous (fun s : Interval => _)
  · simpa [squareUpper] using (continuous_const.max (continuous_const.sub
      (continuous_const.mul continuous_subtype_val)))
  · simpa [squareUpper] using (continuous_const.min (continuous_const.sub
      (continuous_const.mul continuous_subtype_val)))

private theorem squareLower_continuous : Continuous squareLower := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> change Continuous (fun s : Interval => _)
  · simpa [squareLower] using (continuous_const.min (continuous_const.sub
      (continuous_const.mul continuous_subtype_val)))
  · simpa [squareLower] using (continuous_const.max (continuous_const.sub
      (continuous_const.mul continuous_subtype_val)))

theorem squareSweep_continuous : Continuous (fun p : Interval × Interval =>
    squareSweep p.1 p.2) := by
  unfold squareSweep
  exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (squareUpper_continuous.comp continuous_snd)).add
    ((continuous_subtype_val.comp continuous_fst).smul
    (squareLower_continuous.comp continuous_snd)))

private theorem squareUpper_sum (s : Interval) :
    squareUpper s 0 + squareUpper s 1 = 2 - 4 * (s : ℝ) := by
  change max (-1) (1 - 4 * (s : ℝ)) + min 1 (3 - 4 * (s : ℝ)) = _
  by_cases h : -1 ≤ 1 - 4 * (s : ℝ)
  · rw [max_eq_right h, min_eq_left (by linarith)]
    ring
  · rw [max_eq_left (le_of_lt (lt_of_not_ge h)),
      min_eq_right (by linarith)]
    ring

private theorem squareLower_sum (s : Interval) :
    squareLower s 0 + squareLower s 1 = 2 - 4 * (s : ℝ) := by
  simpa [squareLower, squareUpper, add_comm] using squareUpper_sum s

theorem squareSweep_sum (t s : Interval) :
    squareSweep t s 0 + squareSweep t s 1 = 2 - 4 * (s : ℝ) := by
  simp only [squareSweep, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  calc
    _ = (1 - (t : ℝ)) * (squareUpper s 0 + squareUpper s 1) +
        (t : ℝ) * (squareLower s 0 + squareLower s 1) := by ring
    _ = _ := by rw [squareUpper_sum, squareLower_sum]; ring

theorem squareSweep_embedding (t : Interval) :
    Topology.IsEmbedding (squareSweep t) := by
  have hc : Continuous (squareSweep t) :=
    squareSweep_continuous.comp (continuous_const.prodMk continuous_id)
  have hi : Function.Injective (squareSweep t) := by
    intro s u h
    have h0 := congrArg (fun p : Plane => p 0) h
    have h1 := congrArg (fun p : Plane => p 1) h
    have hs := squareSweep_sum t s
    have hu := squareSweep_sum t u
    apply Subtype.ext
    linarith
  exact hc.isClosedEmbedding hi |>.isEmbedding

theorem squareSweep_at_zero (s : Interval) : squareSweep 0 s = squareUpper s := by
  simp [squareSweep]

theorem squareSweep_at_one (s : Interval) : squareSweep 1 s = squareLower s := by
  simp [squareSweep]

theorem squareSweep_left (t : Interval) : squareSweep t 0 = cornerNE := by
  ext i
  fin_cases i <;> simp [squareSweep, squareUpper, squareLower, cornerNE] <;> ring

theorem squareSweep_right (t : Interval) : squareSweep t 1 = cornerSW := by
  have h : squareUpper 1 = cornerSW ∧ squareLower 1 = cornerSW := by
    constructor <;> ext i <;> fin_cases i <;>
      norm_num [squareUpper, squareLower, cornerSW]
  simp [squareSweep, h.1, h.2]
  ext i
  fin_cases i <;> simp [cornerSW] <;> ring

private theorem squareUpper_bounds (s : Interval) :
    -1 ≤ squareUpper s 0 ∧ squareUpper s 0 ≤ 1 ∧
    -1 ≤ squareUpper s 1 ∧ squareUpper s 1 ≤ 1 := by
  have hs0 := s.property.1
  have hs1 := s.property.2
  change -1 ≤ max (-1) (1 - 4 * (s : ℝ)) ∧
    max (-1) (1 - 4 * (s : ℝ)) ≤ 1 ∧
    -1 ≤ min 1 (3 - 4 * (s : ℝ)) ∧
    min 1 (3 - 4 * (s : ℝ)) ≤ 1
  constructor
  · exact le_max_left _ _
  constructor
  · exact max_le (by norm_num) (by linarith)
  constructor
  · exact le_min (by norm_num) (by linarith)
  · exact min_le_left _ _

private theorem squareLower_bounds (s : Interval) :
    -1 ≤ squareLower s 0 ∧ squareLower s 0 ≤ 1 ∧
    -1 ≤ squareLower s 1 ∧ squareLower s 1 ≤ 1 := by
  simpa [squareLower, squareUpper, and_assoc, and_comm, and_left_comm] using
    squareUpper_bounds s

theorem squareSweep_in_closedSquare (t s : Interval) :
    squareSweep t s ∈ Plane.closedSquare 0 1 := by
  obtain ⟨hua0, hua1, hua2, hua3⟩ := squareUpper_bounds s
  obtain ⟨hla0, hla1, hla2, hla3⟩ := squareLower_bounds s
  have ht0 := t.property.1
  have ht1 := t.property.2
  have hx0 : -1 ≤ squareSweep t s 0 ∧ squareSweep t s 0 ≤ 1 := by
    simp only [squareSweep, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    constructor <;> nlinarith
  have hx1 : -1 ≤ squareSweep t s 1 ∧ squareSweep t s 1 ≤ 1 := by
    simp only [squareSweep, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    constructor <;> nlinarith
  simpa only [Plane.closedSquare, Set.mem_setOf_eq, Plane.supDist,
    Plane.supNorm, sub_zero, max_le_iff] using
    (show |squareSweep t s 0| ≤ 1 ∧ |squareSweep t s 1| ≤ 1 from
      ⟨abs_le.mpr hx0, abs_le.mpr hx1⟩)

theorem squareSweep_in_openSquare
    (t s : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1)
    (hs : s ∈ Set.Ioo (0 : Interval) 1) :
    squareSweep t s ∈ Plane.openSquare 0 1 := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht.1
  have ht1 : (t : ℝ) < 1 := by exact_mod_cast ht.2
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs.1
  have hs1 : (s : ℝ) < 1 := by exact_mod_cast hs.2
  obtain ⟨hua0, hua1, hua2, hua3⟩ := squareUpper_bounds s
  obtain ⟨hla0, hla1, hla2, hla3⟩ := squareLower_bounds s
  have hua1' : squareUpper s 0 < 1 := by
    change max (-1) (1 - 4 * (s : ℝ)) < 1
    exact max_lt (by norm_num) (by linarith)
  have hla0' : -1 < squareLower s 0 := by
    change -1 < min 1 (3 - 4 * (s : ℝ))
    exact lt_min (by norm_num) (by linarith)
  have hua2' : -1 < squareUpper s 1 := by
    change -1 < min 1 (3 - 4 * (s : ℝ))
    exact lt_min (by norm_num) (by linarith)
  have hla3' : squareLower s 1 < 1 := by
    change max (-1) (1 - 4 * (s : ℝ)) < 1
    exact max_lt (by norm_num) (by linarith)
  have hx0 : -1 < squareSweep t s 0 ∧ squareSweep t s 0 < 1 := by
    simp only [squareSweep, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    constructor <;> nlinarith
  have hx1 : -1 < squareSweep t s 1 ∧ squareSweep t s 1 < 1 := by
    simp only [squareSweep, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    constructor <;> nlinarith
  simpa only [Plane.openSquare, Set.mem_setOf_eq, Plane.supDist,
    Plane.supNorm, sub_zero, max_lt_iff] using
    (show |squareSweep t s 0| < 1 ∧ |squareSweep t s 1| < 1 from
      ⟨abs_lt.mpr hx0, abs_lt.mpr hx1⟩)

theorem squareUpper_range :
    Set.range squareUpper = sideTop ∪ sideLeft := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · left
      rw [mem_sideTop]
      have hmax : max (-1) (1 - 4 * (s : ℝ)) = 1 - 4 * (s : ℝ) :=
        max_eq_right (by linarith)
      have hmin : min 1 (3 - 4 * (s : ℝ)) = 1 :=
        min_eq_left (by linarith)
      change min 1 (3 - 4 * (s : ℝ)) = 1 ∧
        |max (-1) (1 - 4 * (s : ℝ))| ≤ 1
      rw [hmax, hmin]
      exact ⟨rfl, abs_le.mpr ⟨by linarith [s.property.2], by linarith [s.property.1]⟩⟩
    · right
      rw [mem_sideLeft]
      have hmax : max (-1) (1 - 4 * (s : ℝ)) = -1 :=
        max_eq_left (by linarith)
      have hmin : min 1 (3 - 4 * (s : ℝ)) = 3 - 4 * (s : ℝ) :=
        min_eq_right (by linarith)
      change max (-1) (1 - 4 * (s : ℝ)) = -1 ∧
        |min 1 (3 - 4 * (s : ℝ))| ≤ 1
      rw [hmax, hmin]
      exact ⟨rfl, abs_le.mpr ⟨by linarith [s.property.2], by linarith⟩⟩
  · rintro (hz | hz)
    · rw [mem_sideTop] at hz
      let s : Interval := ⟨(1 - z 0) / 4, by
        rcases (abs_le.mp hz.2) with ⟨h0, h1⟩
        constructor <;> dsimp <;> linarith⟩
      refine ⟨s, ?_⟩
      ext i
      fin_cases i
      · change max (-1) (1 - 4 * (s : ℝ)) = z 0
        have hs : -1 ≤ 1 - 4 * (s : ℝ) := by
          dsimp [s]
          linarith [abs_le.mp hz.2]
        rw [max_eq_right hs]
        dsimp [s]
        ring
      · change min 1 (3 - 4 * (s : ℝ)) = z 1
        rw [hz.1]
        apply min_eq_left
        dsimp [s]
        linarith [abs_le.mp hz.2]
    · rw [mem_sideLeft] at hz
      let s : Interval := ⟨(3 - z 1) / 4, by
        rcases (abs_le.mp hz.2) with ⟨h0, h1⟩
        constructor <;> dsimp <;> linarith⟩
      refine ⟨s, ?_⟩
      ext i
      fin_cases i
      · change max (-1) (1 - 4 * (s : ℝ)) = z 0
        rw [hz.1]
        apply max_eq_left
        dsimp [s]
        linarith [abs_le.mp hz.2]
      · change min 1 (3 - 4 * (s : ℝ)) = z 1
        have hs : 3 - 4 * (s : ℝ) ≤ 1 := by
          dsimp [s]
          linarith [abs_le.mp hz.2]
        rw [min_eq_right hs]
        dsimp [s]
        ring

theorem squareLower_range :
    Set.range squareLower = sideBottom ∪ sideRight := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · right
      rw [mem_sideRight]
      have hmax : max (-1) (1 - 4 * (s : ℝ)) = 1 - 4 * (s : ℝ) :=
        max_eq_right (by linarith)
      have hmin : min 1 (3 - 4 * (s : ℝ)) = 1 :=
        min_eq_left (by linarith)
      change min 1 (3 - 4 * (s : ℝ)) = 1 ∧
        |max (-1) (1 - 4 * (s : ℝ))| ≤ 1
      rw [hmax, hmin]
      exact ⟨rfl, abs_le.mpr ⟨by linarith [s.property.2], by linarith [s.property.1]⟩⟩
    · left
      rw [mem_sideBottom]
      have hmax : max (-1) (1 - 4 * (s : ℝ)) = -1 :=
        max_eq_left (by linarith)
      have hmin : min 1 (3 - 4 * (s : ℝ)) = 3 - 4 * (s : ℝ) :=
        min_eq_right (by linarith)
      change max (-1) (1 - 4 * (s : ℝ)) = -1 ∧
        |min 1 (3 - 4 * (s : ℝ))| ≤ 1
      rw [hmax, hmin]
      exact ⟨rfl, abs_le.mpr ⟨by linarith [s.property.2], by linarith⟩⟩
  · rintro (hz | hz)
    · rw [mem_sideBottom] at hz
      let s : Interval := ⟨(3 - z 0) / 4, by
        rcases (abs_le.mp hz.2) with ⟨h0, h1⟩
        constructor <;> dsimp <;> linarith⟩
      refine ⟨s, ?_⟩
      ext i
      fin_cases i
      · change min 1 (3 - 4 * (s : ℝ)) = z 0
        have hs : 3 - 4 * (s : ℝ) ≤ 1 := by
          dsimp [s]
          linarith [abs_le.mp hz.2]
        rw [min_eq_right hs]
        dsimp [s]
        ring
      · change max (-1) (1 - 4 * (s : ℝ)) = z 1
        rw [hz.1]
        apply max_eq_left
        dsimp [s]
        linarith [abs_le.mp hz.2]
    · rw [mem_sideRight] at hz
      let s : Interval := ⟨(1 - z 1) / 4, by
        rcases (abs_le.mp hz.2) with ⟨h0, h1⟩
        constructor <;> dsimp <;> linarith⟩
      refine ⟨s, ?_⟩
      ext i
      fin_cases i
      · change min 1 (3 - 4 * (s : ℝ)) = z 0
        rw [hz.1]
        apply min_eq_left
        dsimp [s]
        linarith [abs_le.mp hz.2]
      · change max (-1) (1 - 4 * (s : ℝ)) = z 1
        have hs : -1 ≤ 1 - 4 * (s : ℝ) := by
          dsimp [s]
          linarith [abs_le.mp hz.2]
        rw [max_eq_right hs]
        dsimp [s]
        ring

theorem aligned_square_disk_embedded_family
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (d : C(Plane.closedSquare 0 1, ↥F))
    (hd : Topology.IsEmbedding d)
    (σ : Interval ≃ₜ Interval) (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 1)
    (ρ : Interval ≃ₜ Interval) (hρ0 : ρ 0 = 0) (hρ1 : ρ 1 = 1)
    (hupper : ∀ s, d ⟨squareUpper (σ s),
      squareSweep_at_zero (σ s) ▸ squareSweep_in_closedSquare 0 (σ s)⟩ = a s)
    (hlower : ∀ s, d ⟨squareLower (σ s),
      squareSweep_at_one (σ s) ▸ squareSweep_in_closedSquare 1 (σ s)⟩ = b (ρ s))
    (hinside : ∀ z : Plane.closedSquare 0 1,
      z.val ∈ Plane.openSquare 0 1 → (d z).val ∉ frontier F)
    (haClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (a s).val ∉ frontier F)
    (hbClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (b s).val ∉ frontier F) :
    ∃ V : C(Interval × Interval, ↥F),
      (∀ s, V (0,s) = a s) ∧
      (∀ s, V (1,s) = b (ρ s)) ∧
      (∀ t, Topology.IsEmbedding (fun s => V (t,s))) ∧
      (∀ t, V (t,0) = a 0 ∧ V (t,1) = a 1) ∧
      (∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
        (V (t,s)).val ∉ frontier F) := by
  let k : Interval × Interval → Plane.closedSquare 0 1 :=
    fun p => ⟨squareSweep p.1 (σ p.2), squareSweep_in_closedSquare p.1 (σ p.2)⟩
  have hk : Continuous k :=
    (squareSweep_continuous.comp (continuous_fst.prodMk
      (σ.continuous.comp continuous_snd))).subtype_mk _
  let V : C(Interval × Interval, ↥F) := ⟨fun p => d (k p), d.continuous.comp hk⟩
  have hV0 (s : Interval) : V (0,s) = a s := by
    have he : k (0,s) = ⟨squareUpper (σ s),
      squareSweep_at_zero (σ s) ▸ squareSweep_in_closedSquare 0 (σ s)⟩ :=
      Subtype.ext (squareSweep_at_zero (σ s))
    change d (k (0,s)) = a s
    rw [he]
    exact hupper s
  have hV1 (s : Interval) : V (1,s) = b (ρ s) := by
    have he : k (1,s) = ⟨squareLower (σ s),
      squareSweep_at_one (σ s) ▸ squareSweep_in_closedSquare 1 (σ s)⟩ :=
      Subtype.ext (squareSweep_at_one (σ s))
    change d (k (1,s)) = b (ρ s)
    rw [he]
    exact hlower s
  refine ⟨V, hV0, hV1, ?_, ?_, ?_⟩
  · intro t
    have hkemb : Topology.IsEmbedding (fun s : Interval => k (t,s)) := by
      apply Topology.IsEmbedding.of_comp
        (squareSweep_continuous.comp (continuous_const.prodMk σ.continuous) |>.subtype_mk _)
        continuous_subtype_val
      exact (squareSweep_embedding t).comp σ.isEmbedding
    exact hd.comp hkemb
  · intro t
    constructor
    · have he : k (t,0) = k (0,0) := by
        apply Subtype.ext
        simp only [k, hσ0]
        exact (squareSweep_left t).trans (squareSweep_left 0).symm
      change d (k (t,0)) = a 0
      rw [he]
      exact hV0 0
    · have he : k (t,1) = k (0,1) := by
        apply Subtype.ext
        simp only [k, hσ1]
        exact (squareSweep_right t).trans (squareSweep_right 0).symm
      change d (k (t,1)) = a 1
      rw [he]
      exact hV0 1
  · intro t s hs
    by_cases ht0 : t = 0
    · subst t
      rw [hV0]
      exact haClear s hs
    by_cases ht1 : t = 1
    · subst t
      rw [hV1]
      have hρs : ρ s ∈ Set.Ioo (0 : Interval) 1 := by
        have hne0 : ρ s ≠ 0 := by
          intro he
          exact ne_of_gt hs.1 (ρ.injective (he.trans hρ0.symm))
        have hne1 : ρ s ≠ 1 := by
          intro he
          exact ne_of_lt hs.2 (ρ.injective (he.trans hρ1.symm))
        exact ⟨lt_of_le_of_ne (ρ s).property.1 (Ne.symm hne0),
          lt_of_le_of_ne (ρ s).property.2 hne1⟩
      exact hbClear (ρ s) hρs
    have ht : t ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
        lt_of_le_of_ne t.property.2 ht1⟩
    have hσs : σ s ∈ Set.Ioo (0 : Interval) 1 := by
      have hne0 : σ s ≠ 0 := by
        intro he
        exact ne_of_gt hs.1 (σ.injective (he.trans hσ0.symm))
      have hne1 : σ s ≠ 1 := by
        intro he
        exact ne_of_lt hs.2 (σ.injective (he.trans hσ1.symm))
      exact ⟨lt_of_le_of_ne (σ s).property.1 (Ne.symm hne0),
        lt_of_le_of_ne (σ s).property.2 hne1⟩
    exact hinside (k (t,s)) (squareSweep_in_openSquare t (σ s) ht hσs)

theorem square_disk_family_of_boundary_ranges
    {S : Type*} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (d : C(Plane.closedSquare 0 1, ↥F))
    (hd : Topology.IsEmbedding d)
    (hcorner0 : d ⟨cornerNE, squareSweep_left 0 ▸
      squareSweep_in_closedSquare 0 0⟩ = a 0)
    (hcorner1 : d ⟨cornerSW, squareSweep_right 0 ▸
      squareSweep_in_closedSquare 0 1⟩ = a 1)
    (hupper : d '' {z : Plane.closedSquare 0 1 |
      z.val ∈ sideTop ∪ sideLeft} = Set.range a)
    (hlower : d '' {z : Plane.closedSquare 0 1 |
      z.val ∈ sideBottom ∪ sideRight} = Set.range b)
    (hinside : ∀ z : Plane.closedSquare 0 1,
      z.val ∈ Plane.openSquare 0 1 → (d z).val ∉ frontier F)
    (haClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (a s).val ∉ frontier F)
    (hbClear : ∀ s ∈ Set.Ioo (0 : Interval) 1,
      (b s).val ∉ frontier F) :
    ∃ (V : C(Interval × Interval, ↥F)) (ρ : Interval ≃ₜ Interval),
      ρ 0 = 0 ∧ ρ 1 = 1 ∧
      (∀ s, V (0,s) = a s) ∧ (∀ s, V (1,s) = b (ρ s)) ∧
      (∀ t, Topology.IsEmbedding (fun s => V (t,s))) ∧
      (∀ t, V (t,0) = a 0 ∧ V (t,1) = a 1) ∧
      (∀ t s, s ∈ Set.Ioo (0 : Interval) 1 →
        (V (t,s)).val ∉ frontier F) := by
  let ku : C(Interval, Plane.closedSquare 0 1) :=
    ⟨fun s => ⟨squareUpper s,
      squareSweep_at_zero s ▸ squareSweep_in_closedSquare 0 s⟩,
      squareUpper_continuous.subtype_mk _⟩
  let kv : C(Interval, Plane.closedSquare 0 1) :=
    ⟨fun s => ⟨squareLower s,
      squareSweep_at_one s ▸ squareSweep_in_closedSquare 1 s⟩,
      squareLower_continuous.subtype_mk _⟩
  let u : C(Interval, ↥F) := d.comp ku
  let v : C(Interval, ↥F) := d.comp kv
  have hku : Topology.IsEmbedding ku := by
    apply Topology.IsEmbedding.of_comp ku.continuous continuous_subtype_val
    change Topology.IsEmbedding (fun s : Interval => (ku s).val)
    have he : (fun s : Interval => (ku s).val) = squareSweep 0 := by
      funext s
      exact (squareSweep_at_zero s).symm
    rw [he]
    exact squareSweep_embedding 0
  have hkv : Topology.IsEmbedding kv := by
    apply Topology.IsEmbedding.of_comp kv.continuous continuous_subtype_val
    change Topology.IsEmbedding (fun s : Interval => (kv s).val)
    have he : (fun s : Interval => (kv s).val) = squareSweep 1 := by
      funext s
      exact (squareSweep_at_one s).symm
    rw [he]
    exact squareSweep_embedding 1
  have hu : Topology.IsEmbedding u := hd.comp hku
  have hv : Topology.IsEmbedding v := hd.comp hkv
  have huRange : Set.range u = Set.range a := by
    calc
      Set.range u = d '' Set.range ku := by
        exact Set.range_comp (d : Plane.closedSquare 0 1 → ↥F) ku
      _ = d '' {z : Plane.closedSquare 0 1 | z.val ∈ sideTop ∪ sideLeft} := by
        congr 1
        ext z
        constructor
        · rintro ⟨s, rfl⟩
          exact squareUpper_range ▸ ⟨s, rfl⟩
        · intro hz
          have hz' : z.val ∈ Set.range squareUpper := squareUpper_range.symm ▸ hz
          obtain ⟨s, hs⟩ := hz'
          exact ⟨s, Subtype.ext hs⟩
      _ = Set.range a := hupper
  have hvRange : Set.range v = Set.range b := by
    calc
      Set.range v = d '' Set.range kv := by
        exact Set.range_comp (d : Plane.closedSquare 0 1 → ↥F) kv
      _ = d '' {z : Plane.closedSquare 0 1 | z.val ∈ sideBottom ∪ sideRight} := by
        congr 1
        ext z
        constructor
        · rintro ⟨s, rfl⟩
          exact squareLower_range ▸ ⟨s, rfl⟩
        · intro hz
          have hz' : z.val ∈ Set.range squareLower := squareLower_range.symm ▸ hz
          obtain ⟨s, hs⟩ := hz'
          exact ⟨s, Subtype.ext hs⟩
      _ = Set.range b := hlower
  have hu0 : u 0 = a 0 := by
    change d (ku 0) = a 0
    have he : ku 0 = ⟨cornerNE, squareSweep_left 0 ▸
      squareSweep_in_closedSquare 0 0⟩ :=
      Subtype.ext ((squareSweep_at_zero 0).symm.trans (squareSweep_left 0))
    rw [he]
    exact hcorner0
  have hu1 : u 1 = a 1 := by
    change d (ku 1) = a 1
    have he : ku 1 = ⟨cornerSW, squareSweep_right 0 ▸
      squareSweep_in_closedSquare 0 1⟩ :=
      Subtype.ext ((squareSweep_at_zero 1).symm.trans (squareSweep_right 0))
    rw [he]
    exact hcorner1
  have hv0 : v 0 = b 0 := by
    change d (kv 0) = b 0
    have he : kv 0 = ku 0 := by
      apply Subtype.ext
      exact (squareSweep_at_one 0).symm.trans
        ((squareSweep_left 1).trans (squareSweep_left 0).symm) |>.trans
          (squareSweep_at_zero 0)
    rw [he, h0]
    exact hu0
  have hv1 : v 1 = b 1 := by
    change d (kv 1) = b 1
    have he : kv 1 = ku 1 := by
      apply Subtype.ext
      exact (squareSweep_at_one 1).symm.trans
        ((squareSweep_right 1).trans (squareSweep_right 0).symm) |>.trans
          (squareSweep_at_zero 1)
    rw [he, h1]
    exact hu1
  let σ : Interval ≃ₜ Interval :=
    ha.toHomeomorph.trans ((Homeomorph.setCongr huRange.symm).trans
      hu.toHomeomorph.symm)
  have hσ (s : Interval) : u (σ s) = a s := by
    have he := hu.toHomeomorph.apply_symm_apply
      ((Homeomorph.setCongr huRange.symm) (ha.toHomeomorph s))
    exact congrArg Subtype.val he
  have hσ0 : σ 0 = 0 := hu.injective (by rw [hσ, hu0])
  have hσ1 : σ 1 = 1 := hu.injective (by rw [hσ, hu1])
  let τ : Interval ≃ₜ Interval :=
    hv.toHomeomorph.trans ((Homeomorph.setCongr hvRange).trans
      hb.toHomeomorph.symm)
  have hτ (s : Interval) : b (τ s) = v s := by
    have he := hb.toHomeomorph.apply_symm_apply
      ((Homeomorph.setCongr hvRange) (hv.toHomeomorph s))
    exact congrArg Subtype.val he
  have hτ0 : τ 0 = 0 := hb.injective (by rw [hτ, hv0])
  have hτ1 : τ 1 = 1 := hb.injective (by rw [hτ, hv1])
  let ρ : Interval ≃ₜ Interval := σ.trans τ
  have hρ0 : ρ 0 = 0 := by simp [ρ, hσ0, hτ0]
  have hρ1 : ρ 1 = 1 := by simp [ρ, hσ1, hτ1]
  have hupper' (s : Interval) : d ⟨squareUpper (σ s),
      squareSweep_at_zero (σ s) ▸ squareSweep_in_closedSquare 0 (σ s)⟩ = a s :=
    hσ s
  have hlower' (s : Interval) : d ⟨squareLower (σ s),
      squareSweep_at_one (σ s) ▸ squareSweep_in_closedSquare 1 (σ s)⟩ = b (ρ s) := by
    exact (hτ (σ s)).symm
  obtain ⟨V, hV0, hV1, hVemb, hVends, hVclear⟩ :=
    aligned_square_disk_embedded_family a b d hd σ hσ0 hσ1 ρ hρ0 hρ1
      hupper' hlower' hinside haClear hbClear
  exact ⟨V, ρ, hρ0, hρ1, hV0, hV1, hVemb, hVends, hVclear⟩

end RegionalEmbeddedFamily
