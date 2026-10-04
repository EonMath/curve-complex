import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalProfileBandTranslation

open CurveComplex Set Topology

/-- Range-disjoint retained representatives admit an actual open support
    neighborhood inside any prescribed O, without assuming they miss unused
    portions of an old arc. -/
theorem regional_relative_support_neighborhood
    {X : Type} [TopologicalSpace X] [T2Space X]
    (a : C(Interval,X)) {ι : Type} [Fintype ι]
    (retained : ι → C(Interval,X))
    (havoid : ∀ i, Disjoint (Set.range a) (Set.range (retained i)))
    (O : Set X) (hO : IsOpen O) (haO : Set.range a ⊆ O) :
    ∃ U : Set X, IsOpen U ∧ Set.range a ⊆ U ∧ U ⊆ O ∧
      ∀ i, Disjoint U (Set.range (retained i)) := by
  let K : Set X := ⋃ i, Set.range (retained i)
  have hK : IsClosed K :=
    (isCompact_iUnion (fun i => isCompact_range (retained i).continuous)).isClosed
  refine ⟨O ∩ Kᶜ,hO.inter hK.isOpen_compl,?_,Set.inter_subset_left,?_⟩
  · intro y hy
    refine ⟨haO hy,?_⟩
    intro hKy
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hKy
    exact Set.disjoint_left.mp (havoid i) hy hi
  · intro i
    apply Set.disjoint_left.mpr
    intro y hy hret
    exact hy.2 (Set.mem_iUnion.mpr ⟨i,hret⟩)

/-- A profile isotopy fixes every strip fiber on which its displacement is
    zero. This is the exact relative-tail fixity needed by contact cleanup. -/
theorem regional_profile_translation_fixes_zero_fiber
    {X : Type} [TopologicalSpace X]
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,X))
    (ε : C(Interval,ℝ)) (H : AmbientIsotopy X)
    (hband : ∀ (s : Interval) (z : Interval × Set.Icc (-1 : ℝ) 1),
      ∃ w : Set.Icc (-1 : ℝ) 1,
        (w : ℝ) = (z.2 : ℝ) + (s : ℝ)*ε z.1*(1-|(z.2 : ℝ)|) ∧
        H.map (s,E z) = E (z.1,w))
    (t : Interval) (ht : ε t = 0) :
    ∀ s w, H.map (s,E (t,w)) = E (t,w) := by
  intro s w
  obtain ⟨v,hv,hmove⟩ := hband s (t,w)
  have hvw : v = w := Subtype.ext (by simpa [ht] using hv)
  simpa [hvw] using hmove

#print axioms regional_relative_support_neighborhood
#print axioms regional_profile_translation_fixes_zero_fiber
