import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualBandConfinedCoherentChart

open Set Topology Schoenflies CurveComplex

/-- Fixing an entire reference fiber preserves its literal membership, by
injectivity of each time homeomorphism. -/
theorem actual_horizontal_fiber_fixed_isotopy_preserves_fiber
    (H : AmbientIsotopy Plane) (d : ℝ)
    (hFix : ∀ t (z : Plane), z 1 = d → H.map (t,z) = z) :
    ∀ t z, H.map (t,z) 1 = d ↔ z 1 = d := by
  intro t z
  constructor
  · intro hz
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    have hEq : z = H.map (t,z) := e.injective (by rw [he,he,hFix t _ hz])
    exact (congrArg (fun w : Plane => w 1) hEq).trans hz
  · intro hz
    rw [hFix t z hz]
    exact hz

/-- Connected time paths cannot cross a fixed reference fiber. This supplies
actual strip preservation for subsequent local-move source renewal. -/
theorem actual_horizontal_fiber_fixed_isotopy_preserves_open_sides
    (H : AmbientIsotopy Plane) (d : ℝ)
    (hFix : ∀ t (z : Plane), z 1 = d → H.map (t,z) = z) :
    (∀ t z, d < z 1 → d < H.map (t,z) 1) ∧
      (∀ t z, z 1 < d → H.map (t,z) 1 < d) := by
  have hFiber := actual_horizontal_fiber_fixed_isotopy_preserves_fiber H d hFix
  have hSides (z : Plane) (hz : z 1 ≠ d) :
      range (fun t : Interval => H.map (t,z) 1) ⊆ Iio d ∨
        range (fun t : Interval => H.map (t,z) 1) ⊆ Ioi d := by
    have hc : Continuous (fun t : Interval => H.map (t,z) 1) := by fun_prop
    have hCover : range (fun t : Interval => H.map (t,z) 1) ⊆ Iio d ∪ Ioi d := by
      rintro y ⟨t,rfl⟩
      have hn : H.map (t,z) 1 ≠ d := fun he => hz ((hFiber t z).mp he)
      rcases lt_or_gt_of_ne hn with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact (isPreconnected_range hc).subset_or_subset isOpen_Iio isOpen_Ioi
      (Set.disjoint_left.mpr (by
        intro y hy hy'
        change y < d at hy
        change d < y at hy'
        exact lt_asymm hy hy')) hCover
  constructor
  · intro t z hz
    rcases hSides z (ne_of_gt hz) with h | h
    · have h0 := h (mem_range_self (⟨0,by constructor <;> norm_num⟩ : Interval))
      change H.map (⟨0,by constructor <;> norm_num⟩,z) 1 < d at h0
      rw [H.at_zero] at h0
      exact False.elim (lt_asymm hz h0)
    · exact h (mem_range_self t)
  · intro t z hz
    rcases hSides z (ne_of_lt hz) with h | h
    · exact h (mem_range_self t)
    · have h0 := h (mem_range_self (⟨0,by constructor <;> norm_num⟩ : Interval))
      change d < H.map (⟨0,by constructor <;> norm_num⟩,z) 1 at h0
      rw [H.at_zero] at h0
      exact False.elim (lt_asymm hz h0)

#print axioms actual_horizontal_fiber_fixed_isotopy_preserves_fiber
#print axioms actual_horizontal_fiber_fixed_isotopy_preserves_open_sides
