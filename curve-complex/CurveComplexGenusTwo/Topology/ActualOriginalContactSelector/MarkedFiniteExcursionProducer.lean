import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.MarkedSweepContactLocalization

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- All actual old/new contact parameters are finite, including shared
marked endpoints. No cut-open projection or finite movie is assumed. -/
theorem actual_nonloop_all_contact_parameters_finite
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : b.val.map 0 ≠ b.val.map 1)
    (hfinite : (ArcSurgery.crossings M a b).Finite) :
    {t : Interval | b.val.map t ∈ a.val.image}.Finite := by
  have hinj := NonLoopArc.injective ⟨b.val,hne⟩
  apply ((hfinite.preimage hinj.injOn).union ((finite_singleton (1 : Interval)).insert 0)).subset
  intro t ht
  by_cases ht0 : t=0
  · right; simp [ht0]
  by_cases ht1 : t=1
  · right; simp [ht1]
  left
  have hnotmark : b.val.map t ∉ (M.cover.branch : Set S) := fun hm =>
    (b.val.marked_only_at_ends t hm).elim ht0 ht1
  exact ⟨⟨ht,hnotmark⟩,⟨t,rfl⟩,hnotmark⟩

/-- Produce the actual next excursion from an original crossing: its open
parameter interval avoids the old arc, and its terminal event is either
another original crossing, a shared marked endpoint, or the new endpoint.
The finite event set is constructed solely for this FIXED pair. -/
theorem actual_next_crossing_excursion_parameter
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : b.val.map 0 ≠ b.val.map 1)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (r : Interval) (hr : b.val.map r ∈ ArcSurgery.crossings M a b) :
    ∃ s : Interval, r < s ∧
      (s=1 ∨ b.val.map s ∈ ArcSurgery.crossings M a b ∨
        (b.val.map s ∈ a.val.image ∧ b.val.map s ∈ M.cover.branch)) ∧
      ∀ t : Interval, r < t → t < s → b.val.map t ∉ a.val.image := by
  classical
  let A : Set Interval := {t | b.val.map t ∈ a.val.image} ∪ {0,1}
  have hAf : A.Finite := (actual_nonloop_all_contact_parameters_finite M a b hne hfinite).union
    ((finite_singleton (1 : Interval)).insert 0)
  have hrne1 : r ≠ 1 := by
    intro he; subst r
    exact hr.2.2 b.val.end_marked
  have hrlt : r < (1 : Interval) := lt_of_le_of_ne r.property.2 hrne1
  have hneSet : (A ∩ Ioi r).Nonempty := ⟨1,Or.inr (by simp),hrlt⟩
  obtain ⟨s,hs,hsmin⟩ := (hAf.subset inter_subset_left).isCompact.exists_isLeast hneSet
  refine ⟨s,hs.2,?_,?_⟩
  · by_cases hs1 : s=1
    · exact Or.inl hs1
    right
    have hs0 : s ≠ 0 := by
      intro he; subst s
      exact (not_lt_of_ge r.property.1) hs.2
    have hcontact : b.val.map s ∈ a.val.image := by
      rcases hs.1 with hc | he
      · exact hc
      · rcases mem_insert_iff.mp he with he | he
        · exact False.elim (hs0 he)
        · exact False.elim (hs1 (mem_singleton_iff.mp he))
    by_cases hm : b.val.map s ∈ M.cover.branch
    · exact Or.inr ⟨hcontact,hm⟩
    · exact Or.inl ⟨⟨hcontact,hm⟩,⟨s,rfl⟩,hm⟩
  · intro t hrt hts ht
    have htA : t ∈ A ∩ Ioi r := ⟨Or.inl ht,hrt⟩
    exact (not_lt_of_ge (hsmin htA)) hts

/-- The next parameter event produces an actual embedded excursion, with
interior in the complement of the fixed old arc. This is the concrete
path needed before constructing the cut-open bank lift. -/
theorem actual_next_crossing_embedded_excursion
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : b.val.map 0 ≠ b.val.map 1)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (r : Interval) (hr : b.val.map r ∈ ArcSurgery.crossings M a b) :
    ∃ f : C(Interval,S), IsEmbedding f ∧ range f ⊆ b.val.image ∧
      f 0 = b.val.map r ∧
      (f 1 = b.val.map 1 ∨ f 1 ∈ ArcSurgery.crossings M a b ∨
        (f 1 ∈ a.val.image ∧ f 1 ∈ M.cover.branch)) ∧
      Disjoint (f '' Ioo (0 : Interval) 1) a.val.image := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨s,hrs,hend,hoff⟩ := actual_next_crossing_excursion_parameter M a b hne hfinite r hr
  let affine : Interval → Interval := fun t =>
    ⟨(1-t.val)*r.val+t.val*s.val,by constructor <;>
      nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,s.property.1,s.property.2]⟩
  let f : C(Interval,S) := ⟨b.val.map ∘ affine,b.val.continuous.comp (by fun_prop)⟩
  have hf0 : f 0 = b.val.map r := by
    apply congrArg b.val.map; apply Subtype.ext; simp [affine]
  have hf1 : f 1 = b.val.map s := by
    apply congrArg b.val.map; apply Subtype.ext; simp [affine]
  have hinj : Function.Injective f := by
    intro t u he
    have hv := congrArg Subtype.val (NonLoopArc.injective ⟨b.val,hne⟩ he)
    apply Subtype.ext
    have hrsv : r.val < s.val := hrs
    dsimp [affine] at hv
    nlinarith
  refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,?_,hf0,?_,?_⟩
  · rintro p ⟨t,rfl⟩; exact ⟨affine t,rfl⟩
  · rw [hf1]
    rcases hend with rfl | hend
    · exact Or.inl rfl
    · exact Or.inr hend
  · apply disjoint_left.mpr
    rintro p ⟨t,ht,hpt⟩ hpA
    have hrsv : r.val < s.val := hrs
    have hrt : r < affine t := by
      change r.val < (1-t.val)*r.val+t.val*s.val
      have ht0 : 0 < t.val := ht.1
      nlinarith
    have hts : affine t < s := by
      change (1-t.val)*r.val+t.val*s.val < s.val
      have ht1 : t.val < 1 := ht.2
      nlinarith
    apply hoff (affine t) hrt hts
    change f t ∈ a.val.image
    rw [hpt]
    exact hpA

end CurveComplex.HyperellipticModel
