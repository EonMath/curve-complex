import Mathlib

namespace CurveComplex.BranchedDoubleCover

def intervalAffine (a b : unitInterval) (u : unitInterval) : unitInterval :=
  ⟨(1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ), by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr u.property.2) a.property.1)
        (mul_nonneg u.property.1 b.property.1)
    · nlinarith [a.property.2, b.property.2,
        mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr a.property.2),
        mul_nonneg u.property.1 (sub_nonneg.mpr b.property.2)]⟩

def actualSubpath {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x y) (a b : unitInterval) : Path (γ a) (γ b) where
  toFun u := γ (intervalAffine a b u)
  continuous_toFun := γ.continuous.comp (by
    apply Continuous.subtype_mk
    fun_prop)
  source' := by simp [intervalAffine]
  target' := by simp [intervalAffine]

theorem intervalAffine_mem_Icc {a b : unitInterval} (hab : a ≤ b)
    (u : unitInterval) : intervalAffine a b u ∈ Set.Icc a b := by
  constructor
  · change (a : ℝ) ≤ (1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)
    have hh : (a : ℝ) ≤ (b : ℝ) := hab
    nlinarith [mul_nonneg u.property.1 (sub_nonneg.mpr hh)]
  · change (1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ) ≤ (b : ℝ)
    have hh : (a : ℝ) ≤ (b : ℝ) := hab
    nlinarith [mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr hh)]

def intervalSegment (a b : unitInterval) : Path a b where
  toFun := intervalAffine a b
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop
  source' := by apply Subtype.ext; simp [intervalAffine]
  target' := by apply Subtype.ext; simp [intervalAffine]

theorem actualSubpath_trans_homotopic
    {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    (a b c : unitInterval) :
    ((actualSubpath γ a b).trans (actualSubpath γ b c)).Homotopic
      (actualSubpath γ a c) := by
  letI : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have hh := (SimplyConnectedSpace.paths_homotopic
    ((intervalSegment a b).trans (intervalSegment b c)) (intervalSegment a c)).map
      (⟨γ, γ.continuous⟩ : C(unitInterval, X))
  change (((intervalSegment a b).trans (intervalSegment b c)).map γ.continuous).Homotopic
    ((intervalSegment a c).map γ.continuous) at hh
  rw [Path.map_trans] at hh
  exact hh

noncomputable def actualSegmentChain {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x y) (t : ℕ → unitInterval) :
    (n : ℕ) → Path (γ (t 0)) (γ (t n))
  | 0 => Path.refl (γ (t 0))
  | n + 1 => (actualSegmentChain γ t n).trans (actualSubpath γ (t n) (t (n + 1)))

theorem actualSegmentChain_homotopic
    {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x y) (t : ℕ → unitInterval) (n : ℕ) :
    (actualSegmentChain γ t n).Homotopic (actualSubpath γ (t 0) (t n)) := by
  induction n with
  | zero =>
    letI : ContractibleSpace unitInterval :=
      (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
    exact (SimplyConnectedSpace.paths_homotopic (Path.refl (t 0))
      (intervalSegment (t 0) (t 0))).map (⟨γ, γ.continuous⟩ : C(unitInterval, X))
  | succ n ih =>
    exact (ih.hcomp (Path.Homotopic.refl _)).trans
      (actualSubpath_trans_homotopic γ (t 0) (t n) (t (n + 1)))

/-- Every actual loop has a finite decomposition into actual local paths
inside members of any open cover of its actual compact image. The paths
are restrictions of the given loop, not separately assumed representatives. -/
theorem actual_loop_finite_open_cover_subdivision
    {X ι : Type*} [TopologicalSpace X] {x : X} (γ : Path x x)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.range γ ⊆ ⋃ i, U i) :
    ∃ N : ℕ, 0 < N ∧ ∃ t : ℕ → unitInterval,
      t 0 = 0 ∧ t N = 1 ∧ Monotone t ∧
      (∀ n ≥ N, t n = 1) ∧
      ∀ i < N, ∃ j, Set.range (actualSubpath γ (t i) (t (i + 1))) ⊆ U j := by
  obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hU i).preimage γ.continuous) (by
        intro u hu
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self u))
        exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hpos : 0 < N := by
    by_contra hn
    have hz : N = 0 := Nat.eq_zero_of_not_pos hn
    have he := hN N le_rfl
    rw [hz, ht0] at he
    exact zero_ne_one he
  refine ⟨N, hpos, t, ht0, hN N le_rfl, hmono, hN, ?_⟩
  intro i hi
  obtain ⟨j, hj⟩ := hsub i
  refine ⟨j, ?_⟩
  rintro z ⟨u, rfl⟩
  exact hj (intervalAffine_mem_Icc (hmono (Nat.le_succ i)) u)

theorem actual_loop_equals_segment_chain_in_fundamentalGroup
    {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x)
    (t : ℕ → unitInterval) (N : ℕ) (ht0 : t 0 = 0) (htN : t N = 1) :
    ∃ h0 : x = γ (t 0), ∃ hN : x = γ (t N),
      Path.Homotopic.Quotient.mk ((actualSegmentChain γ t N).cast h0 hN) =
        Path.Homotopic.Quotient.mk γ := by
  have h0 : x = γ (t 0) := by rw [ht0]; exact γ.source.symm
  have hN : x = γ (t N) := by rw [htN]; exact γ.target.symm
  refine ⟨h0, hN, ?_⟩
  apply Path.Homotopic.Quotient.eq.mpr
  have hh := (actualSegmentChain_homotopic γ t N).pathCast h0 hN
  have he : (actualSubpath γ (t 0) (t N)).cast h0 hN = γ := by
    ext u
    change γ (intervalAffine (t 0) (t N) u) = γ u
    rw [ht0, htN]
    congr 1
    apply Subtype.ext
    simp [intervalAffine]
  rw [he] at hh
  exact hh

end CurveComplex.BranchedDoubleCover
