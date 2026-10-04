import CurveComplexGenusTwo.Foundations.Definitions

open Set Topology

namespace ActualHarerDiskGluing

/-- A continuous map on a compact presentation descends through an equal
fiber relation, producing an embedding with the exact original image. -/
theorem compact_kernel_transport
    {X Y S : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace S] [T2Space S]
    (a : C(X,Y)) (b : C(X,S)) (ha : Function.Surjective a)
    (hker : ∀ x y, a x = a y ↔ b x = b y) :
    ∃ f : C(Y,S), IsEmbedding f ∧ range f = range b ∧ ∀ x, f (a x) = b x := by
  classical
  have hsurj := ha
  choose r hr using hsurj
  let f : Y → S := fun y => b (r y)
  have hf (x : X) : f (a x) = b x :=
    (hker _ _).mp (hr _)
  have hquot : IsQuotientMap a := a.continuous.isClosedMap.isQuotientMap a.continuous ha
  have hc : Continuous f := hquot.continuous_iff.mpr (by
    have he : f ∘ a = b := funext hf
    rw [he]
    exact b.continuous)
  have hi : Function.Injective f := by
    intro x y he
    have he' := (hker _ _).mpr he
    exact (hr x).symm.trans (he'.trans (hr y))
  haveI : CompactSpace Y := isCompact_univ_iff.mp (by simpa only [ha.range_eq, Set.image_univ] using isCompact_univ.image a.continuous)
  refine ⟨⟨f,hc⟩,(hc.isClosedEmbedding hi).isEmbedding,?_,hf⟩
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨r x,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨a x,hf x⟩

/-- Two embedded endpoint-matched pairs have the same sum-presentation fibers. -/
theorem clean_pair_sum_kernel
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (a b : CurveComplex.Interval → S) (c d : CurveComplex.Interval → T)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hc : Function.Injective c) (hd : Function.Injective d)
    (ha0 : a 0 = b 0) (ha1 : a 1 = b 1)
    (hc0 : c 0 = d 0) (hc1 : c 1 = d 1)
    (hab : ∀ s t, a s = b t → (s=0 ∧ t=0) ∨ (s=1 ∧ t=1))
    (hcd : ∀ s t, c s = d t → (s=0 ∧ t=0) ∨ (s=1 ∧ t=1)) :
    ∀ x y : CurveComplex.Interval ⊕ CurveComplex.Interval,
      Sum.elim a b x = Sum.elim a b y ↔ Sum.elim c d x = Sum.elim c d y := by
  have cross (s t : CurveComplex.Interval) : a s = b t ↔ c s = d t := by
    constructor
    · intro h
      rcases hab s t h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hc0
      · exact hc1
    · intro h
      rcases hcd s t h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ha0
      · exact ha1
  intro x y
  cases x with
  | inl s =>
    cases y with
    | inl t => exact ⟨fun h => congrArg c (ha h),fun h => congrArg a (hc h)⟩
    | inr t => exact cross s t
  | inr s =>
    cases y with
    | inl t => exact ⟨fun h => ((cross t s).mp h.symm).symm,
        fun h => ((cross t s).mpr h.symm).symm⟩
    | inr t => exact ⟨fun h => congrArg d (hb h),fun h => congrArg b (hd h)⟩

end ActualHarerDiskGluing
