import CurveComplexGenusTwo.Filtration.Geometry.MarkedArcPrimitives

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Removing a marked endpoint leaves a connected half-open actual arc. -/
theorem nonloop_image_remove_start_connected (M : HyperellipticModel E S)
    (a : NonLoopArc M) : IsConnected (a.val.image \ {a.val.map 0}) := by
  have heq : a.val.image \ {a.val.map 0} = a.val.map '' Set.Ioi (0 : Interval) := by
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hn⟩
      refine ⟨t, ?_, rfl⟩
      have ht : (t : ℝ) ≠ 0 := by
        intro h
        have he : t = (0 : Interval) := Subtype.ext h
        exact hn (Set.mem_singleton_iff.mpr (congrArg a.val.map he))
      change (0 : ℝ) < t.val
      exact lt_of_le_of_ne' t.property.1 ht
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      intro he
      have he' : t = (0 : Interval) := a.injective (Set.mem_singleton_iff.mp he)
      simpa [he'] using ht
  rw [heq]
  have hc : IsConnected (Set.Ioi (0 : Interval)) :=
    ⟨⟨1, by norm_num⟩, isPreconnected_Ioi⟩
  exact hc.image a.val.map a.val.continuous.continuousOn

/-- The analogous actual half-open arc after removal of its last endpoint. -/
theorem nonloop_image_remove_end_connected (M : HyperellipticModel E S)
    (a : NonLoopArc M) : IsConnected (a.val.image \ {a.val.map 1}) := by
  have heq : a.val.image \ {a.val.map 1} = a.val.map '' Set.Iio (1 : Interval) := by
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hn⟩
      refine ⟨t, ?_, rfl⟩
      have ht : (t : ℝ) ≠ 1 := by
        intro h
        have he : t = (1 : Interval) := Subtype.ext h
        exact hn (Set.mem_singleton_iff.mpr (congrArg a.val.map he))
      change t.val < (1 : ℝ)
      exact lt_of_le_of_ne t.property.2 ht
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      intro he
      have he' : t = (1 : Interval) := a.injective (Set.mem_singleton_iff.mp he)
      simpa [he'] using ht
  rw [heq]
  have hc : IsConnected (Set.Iio (1 : Interval)) :=
    ⟨⟨0, by norm_num⟩, isPreconnected_Iio⟩
  exact hc.image a.val.map a.val.continuous.continuousOn

/-- Corollary 9.3's punctured-object input: a mark cannot cut the interior of a non-loop arc. -/
theorem nonloop_image_remove_mark_connected (M : HyperellipticModel E S)
    (a : NonLoopArc M) (b : S) (hb : b ∈ M.cover.branch) :
    IsConnected (a.val.image \ {b}) := by
  by_cases h0 : b = a.val.map 0
  · rw [h0]
    exact nonloop_image_remove_start_connected M a
  by_cases h1 : b = a.val.map 1
  · rw [h1]
    exact nonloop_image_remove_end_connected M a
  have hbimage : b ∉ a.val.image := by
    rintro ⟨t, ht⟩
    have hmarked : a.val.map t ∈ M.cover.branch := ht.symm ▸ hb
    rcases a.val.marked_only_at_ends t hmarked with he | he
    · subst t
      exact h0 ht.symm
    · subst t
      exact h1 ht.symm
  have heq : a.val.image \ {b} = a.val.image := by
    ext x
    constructor
    · exact And.left
    · intro hx
      refine ⟨hx, ?_⟩
      intro he
      exact hbimage ((Set.mem_singleton_iff.mp he) ▸ hx)
  rw [heq]
  exact markedArc_image_connected a.val

/-- A loop object with its marked base removed is an actual connected open arc. -/
theorem loop_image_remove_base_connected (M : HyperellipticModel E S)
    (a : MarkedArc M) (ha : a.map 0 = a.map 1) :
    IsConnected (a.image \ {a.map 0}) := by
  have heq : a.image \ {a.map 0} = a.map '' Set.Ioo (0 : Interval) 1 := by
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hn⟩
      refine ⟨t, ?_, rfl⟩
      have ht0 : (t : ℝ) ≠ 0 := by
        intro h
        exact hn (Set.mem_singleton_iff.mpr (congrArg a.map (Subtype.ext h)))
      have ht1 : (t : ℝ) ≠ 1 := by
        intro h
        exact hn (Set.mem_singleton_iff.mpr
          ((congrArg a.map (show t = (1 : Interval) from Subtype.ext h)).trans ha.symm))
      change (0 : ℝ) < t.val ∧ t.val < (1 : ℝ)
      exact ⟨lt_of_le_of_ne' t.property.1 ht0, lt_of_le_of_ne t.property.2 ht1⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      intro he
      have he' := a.injective_except_loop_closure t 0 (Set.mem_singleton_iff.mp he)
      rcases he' with he' | he' | he'
      · simpa [he'] using ht.1
      · simpa [he'.1] using ht.1
      · simpa [he'.1] using ht.2
  rw [heq]
  have hc : IsConnected (Set.Ioo (0 : Interval) 1) := by
    refine ⟨?_, isPreconnected_Ioo⟩
    refine ⟨⟨(1 : ℝ) / 2, by norm_num⟩, ?_⟩
    change (0 : ℝ) < 1 / 2 ∧ (1 : ℝ) / 2 < 1
    norm_num
  exact hc.image a.map a.continuous.continuousOn


/-- For loops or non-loops, an original branch mark never disconnects an arc object. -/
theorem markedArc_image_remove_mark_connected (M : HyperellipticModel E S)
    (a : MarkedArc M) (b : S) (hb : b ∈ M.cover.branch) :
    IsConnected (a.image \ {b}) := by
  by_cases ha : a.map 0 = a.map 1
  · by_cases hbase : b = a.map 0
    · rw [hbase]
      exact loop_image_remove_base_connected M a ha
    · have hbimage : b ∉ a.image := by
        rintro ⟨t, ht⟩
        have hmarked : a.map t ∈ M.cover.branch := ht.symm ▸ hb
        rcases a.marked_only_at_ends t hmarked with he | he
        · subst t
          exact hbase ht.symm
        · subst t
          exact hbase (ht.symm.trans ha.symm)
      have heq : a.image \ {b} = a.image := by
        ext x
        constructor
        · exact And.left
        · intro hx
          exact ⟨hx, fun he => hbimage ((Set.mem_singleton_iff.mp he) ▸ hx)⟩
      rw [heq]
      exact markedArc_image_connected a
  · exact nonloop_image_remove_mark_connected M ⟨a, ha⟩ b hb


/-- Every actual arc image is nontrivial, including loops with coincident ends. -/
theorem markedArc_image_nontrivial (M : HyperellipticModel E S) (a : MarkedArc M) :
    a.image.Nontrivial := by
  let m : Interval := ⟨(1 : ℝ) / 2, by norm_num⟩
  refine ⟨a.map 0, ⟨0, rfl⟩, a.map m, ⟨m, rfl⟩, ?_⟩
  intro he
  rcases a.injective_except_loop_closure 0 m he with h | h | h
  · have hh := congrArg Subtype.val h
    norm_num [m] at hh
  · have hh := congrArg Subtype.val h.2
    norm_num [m] at hh
  · have hh := congrArg Subtype.val h.1
    norm_num at hh

/-- An object arc loses no closure point when one intersection mark is removed. -/
theorem markedArc_puncture_dense (M : HyperellipticModel E S) (a : MarkedArc M) (b : S) :
    a.image ⊆ closure (a.image \ {b}) := by
  letI : T2Space S := M.sphere.symm.t2Space
  intro x hx
  by_cases he : x = b
  · subst x
    rw [mem_closure_iff_clusterPt, ← accPt_principal_iff_clusterPt]
    exact (markedArc_image_connected a).isPreconnected.preperfect_of_nontrivial
      (markedArc_image_nontrivial M a) b hx
  · exact subset_closure ⟨hx, he⟩


end CurveComplex.HyperellipticModel
