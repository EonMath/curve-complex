import CurveComplexGenusTwo.Topology.CapBandGeometry.BandRegularity

open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

/-- Literal longitudinal slice of one supplied embedded band. -/
def bandSlice {S : Type*} (F : I × BandWidth → S) (J : Set ℝ) : Set S :=
  F '' {p | (p.1 : ℝ) ∈ J}

theorem bandSlice_mem_iff {S : Type*} (F : I × BandWidth → S)
    (hF : Function.Injective F) (J : Set ℝ) (p : I × BandWidth) :
    F p ∈ bandSlice F J ↔ (p.1 : ℝ) ∈ J := by
  constructor
  · rintro ⟨q, hq, he⟩
    exact hF he ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem bandSlice_closed {S : Type*} [TopologicalSpace S] [T2Space S]
    (F : I × BandWidth → S) (hF : IsEmbedding F)
    (J : Set ℝ) (hJ : IsClosed J) : IsClosed (bandSlice F J) := by
  have hclosed : IsClosed {p : I × BandWidth | (p.1 : ℝ) ∈ J} :=
    hJ.preimage (continuous_subtype_val.comp continuous_fst)
  exact (hclosed.isCompact.image hF.continuous).isClosed

/-- Only parameter endpoints of an attached band meet the square. -/
theorem first_mem_square_iff {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (p : I × BandWidth) : B.first p ∈ Set.range D.square ↔ p.1 = 0 ∨ p.1 = 1 := by
  constructor
  · intro hp
    have hmeet : B.first p ∈ Set.range B.first ∩ Set.range D.square :=
      ⟨Set.mem_range_self p, hp⟩
    rw [B.first_square] at hmeet
    rcases hmeet with ⟨u, hu⟩ | ⟨u, hu⟩
    · left
      exact congrArg Prod.fst (B.first_embedded.injective (hu.symm.trans (B.first_bottom u).symm))
    · right
      exact congrArg Prod.fst (B.first_embedded.injective (hu.symm.trans (B.first_top u).symm))
  · rintro (h0 | h1)
    · have he : p = (0, p.2) := Prod.ext h0 rfl
      rw [he, B.first_bottom]
      exact Set.mem_range_self _
    · have he : p = (1, p.2) := Prod.ext h1 rfl
      rw [he, B.first_top]
      exact Set.mem_range_self _

theorem second_mem_square_iff {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (p : I × BandWidth) : B.second p ∈ Set.range D.square ↔ p.1 = 0 ∨ p.1 = 1 := by
  constructor
  · intro hp
    have hmeet : B.second p ∈ Set.range B.second ∩ Set.range D.square :=
      ⟨Set.mem_range_self p, hp⟩
    rw [B.second_square] at hmeet
    rcases hmeet with ⟨u, hu⟩ | ⟨u, hu⟩
    · left
      exact congrArg Prod.fst (B.second_embedded.injective (hu.symm.trans (B.second_left u).symm))
    · right
      exact congrArg Prod.fst (B.second_embedded.injective (hu.symm.trans (B.second_right u).symm))
  · rintro (h0 | h1)
    · have he : p = (0, p.2) := Prod.ext h0 rfl
      rw [he, B.second_left]
      exact Set.mem_range_self _
    · have he : p = (1, p.2) := Prod.ext h1 rfl
      rw [he, B.second_right]
      exact Set.mem_range_self _

/-- The actual neighborhood, without any replacement witness. -/
def bandUnion {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) : Set S :=
  Set.range D.square ∪ Set.range B.first ∪ Set.range B.second

/-- Remove compact middle slabs: what remains is the square with four end collars. -/
def squareCollars {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) : Set S :=
  bandUnion D B \ (bandSlice B.first (Icc (1/3 : ℝ) (2/3)) ∪
    bandSlice B.second (Icc (1/3 : ℝ) (2/3)))

/-- The two middle-band sets include their transverse boundary sides. -/
def middleBands {S : Type} [TopologicalSpace S] {a b : Curve S}
    {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D) : Set S :=
  bandSlice B.first (Ioo (1/4 : ℝ) (3/4)) ∪
    bandSlice B.second (Ioo (1/4 : ℝ) (3/4))

theorem squareCollars_relative_open {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    IsOpen ((Subtype.val : bandUnion D B → S) ⁻¹' squareCollars D B) := by
  have hclosed : IsClosed (bandSlice B.first (Icc (1/3 : ℝ) (2/3)) ∪
      bandSlice B.second (Icc (1/3 : ℝ) (2/3))) :=
    (bandSlice_closed B.first B.first_embedded _ isClosed_Icc).union
      (bandSlice_closed B.second B.second_embedded _ isClosed_Icc)
  have heq : ((Subtype.val : bandUnion D B → S) ⁻¹' squareCollars D B) =
      ((Subtype.val : bandUnion D B → S) ⁻¹'
        (bandSlice B.first (Icc (1/3 : ℝ) (2/3)) ∪
          bandSlice B.second (Icc (1/3 : ℝ) (2/3))))ᶜ := by
    ext x
    simp [squareCollars, x.property]
  rw [heq]
  exact (hclosed.preimage continuous_subtype_val).isOpen_compl

/-- The literal cover needed to compute homology, with no rank assumption. -/
theorem squareCollars_middleBands_cover {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    squareCollars D B ∪ middleBands B = bandUnion D B := by
  apply subset_antisymm
  · rintro x (hx | hx)
    · exact hx.1
    · rcases hx with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
      · exact Or.inl (Or.inr (Set.mem_range_self _))
      · exact Or.inr (Set.mem_range_self _)
  · intro x hx
    by_cases hm : x ∈ (bandSlice B.first (Icc (1/3 : ℝ) (2/3)) ∪
        bandSlice B.second (Icc (1/3 : ℝ) (2/3)))
    · right
      rcases hm with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
      · left
        exact ⟨p, ⟨by linarith [hp.1], by linarith [hp.2]⟩, rfl⟩
      · right
        exact ⟨p, ⟨by linarith [hp.1], by linarith [hp.2]⟩, rfl⟩
    · exact Or.inl ⟨hx, hm⟩

end CurveComplex.CapBandGeometry

namespace CurveComplex.CapBandGeometry

theorem first_not_in_second_slice {S : Type} [TopologicalSpace S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D)
    (p : I × BandWidth) (J : Set ℝ) : B.first p ∉ bandSlice B.second J := by
  intro hx
  exact Set.disjoint_left.mp B.bands_disjoint (Set.mem_range_self p)
    (Set.image_subset_range _ _ hx)

theorem second_not_in_first_slice {S : Type} [TopologicalSpace S]
    {a b : Curve S} {D : OneCrossingBandBase a b} (B : CompatibleOutsideBands D)
    (p : I × BandWidth) (J : Set ℝ) : B.second p ∉ bandSlice B.first J := by
  intro hx
  exact Set.disjoint_left.mp B.bands_disjoint (Set.image_subset_range _ _ hx)
    (Set.mem_range_self p)

theorem first_mem_squareCollars_iff {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (p : I × BandWidth) : B.first p ∈ squareCollars D B ↔
      (p.1 : ℝ) < 1/3 ∨ 2/3 < (p.1 : ℝ) := by
  have hN : B.first p ∈ bandUnion D B := Or.inl (Or.inr (Set.mem_range_self p))
  simp only [squareCollars, Set.mem_diff, hN, true_and, Set.mem_union,
    bandSlice_mem_iff _ B.first_embedded.injective,
    first_not_in_second_slice B p, or_false, Set.mem_Icc]
  constructor
  · intro h
    by_cases hlo : (p.1 : ℝ) < 1/3
    · exact Or.inl hlo
    · exact Or.inr (lt_of_not_ge (fun hh => h ⟨le_of_not_gt hlo, hh⟩))
  · rintro (h | h) hp
    · linarith [hp.1]
    · linarith [hp.2]

theorem second_mem_squareCollars_iff {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (p : I × BandWidth) : B.second p ∈ squareCollars D B ↔
      (p.1 : ℝ) < 1/3 ∨ 2/3 < (p.1 : ℝ) := by
  have hN : B.second p ∈ bandUnion D B := Or.inr (Set.mem_range_self p)
  simp only [squareCollars, Set.mem_diff, hN, true_and, Set.mem_union,
    bandSlice_mem_iff _ B.second_embedded.injective,
    second_not_in_first_slice B p, false_or, Set.mem_Icc]
  constructor
  · intro h
    by_cases hlo : (p.1 : ℝ) < 1/3
    · exact Or.inl hlo
    · exact Or.inr (lt_of_not_ge (fun hh => h ⟨le_of_not_gt hlo, hh⟩))
  · rintro (h | h) hp
    · linarith [hp.1]
    · linarith [hp.2]

/-- The relative complement of the two middle rectangles is a compact union
of the actual square and four closed end strips. -/
theorem middleBands_relative_complement {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    bandUnion D B \ middleBands B = Set.range D.square ∪
      bandSlice B.first (Iic (1/4 : ℝ) ∪ Ici (3/4)) ∪
      bandSlice B.second (Iic (1/4 : ℝ) ∪ Ici (3/4)) := by
  have houtside (t : ℝ) : t ∉ Ioo (1/4 : ℝ) (3/4) ↔
      t ∈ Iic (1/4 : ℝ) ∪ Ici (3/4) := by
    simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro h
      by_cases hlo : t ≤ 1/4
      · exact Or.inl hlo
      · exact Or.inr (le_of_not_gt (fun hhi => h ⟨lt_of_not_ge hlo, hhi⟩))
    · rintro (h | h) hp
      · linarith [hp.1]
      · linarith [hp.2]
  have hsquare : Disjoint (Set.range D.square) (middleBands B) := by
    apply Set.disjoint_left.mpr
    rintro x hx (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · rcases (first_mem_square_iff D B p).mp hx with h | h
      · have ht : (p.1 : ℝ) = 0 := congrArg Subtype.val h
        linarith [hp.1]
      · have ht : (p.1 : ℝ) = 1 := congrArg Subtype.val h
        linarith [hp.2]
    · rcases (second_mem_square_iff D B p).mp hx with h | h
      · have ht : (p.1 : ℝ) = 0 := congrArg Subtype.val h
        linarith [hp.1]
      · have ht : (p.1 : ℝ) = 1 := congrArg Subtype.val h
        linarith [hp.2]
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    rcases hx with (hx | ⟨p, rfl⟩) | ⟨p, rfl⟩
    · exact Or.inl (Or.inl hx)
    · refine Or.inl (Or.inr ⟨p, (houtside _).mp ?_, rfl⟩)
      intro hp
      exact hnot (Or.inl ⟨p, hp, rfl⟩)
    · refine Or.inr ⟨p, (houtside _).mp ?_, rfl⟩
      intro hp
      exact hnot (Or.inr ⟨p, hp, rfl⟩)
  · rintro ((hx | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩)
    · exact ⟨Or.inl (Or.inl hx), Set.disjoint_left.mp hsquare hx⟩
    · refine ⟨Or.inl (Or.inr (Set.mem_range_self p)), ?_⟩
      rintro (hm | hm)
      · exact (houtside _).mpr hp ((bandSlice_mem_iff _ B.first_embedded.injective _ p).mp hm)
      · exact first_not_in_second_slice B p _ hm
    · refine ⟨Or.inr (Set.mem_range_self p), ?_⟩
      rintro (hm | hm)
      · exact second_not_in_first_slice B p _ hm
      · exact (houtside _).mpr hp ((bandSlice_mem_iff _ B.second_embedded.injective _ p).mp hm)

theorem middleBands_relative_open {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    IsOpen ((Subtype.val : bandUnion D B → S) ⁻¹' middleBands B) := by
  have hclosed : IsClosed (bandUnion D B \ middleBands B) := by
    rw [middleBands_relative_complement D B]
    exact ((isCompact_range D.square_embedded.continuous).isClosed.union
      (bandSlice_closed B.first B.first_embedded _ (isClosed_Iic.union isClosed_Ici))).union
      (bandSlice_closed B.second B.second_embedded _ (isClosed_Iic.union isClosed_Ici))
  have heq : ((Subtype.val : bandUnion D B → S) ⁻¹' middleBands B) =
      ((Subtype.val : bandUnion D B → S) ⁻¹' (bandUnion D B \ middleBands B))ᶜ := by
    ext x
    simp
  rw [heq]
  exact (hclosed.preimage continuous_subtype_val).isOpen_compl

/-- The overlap is exactly the four end-of-middle rectangular windows. -/
theorem squareCollars_middleBands_intersection {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    squareCollars D B ∩ middleBands B =
      bandSlice B.first (Ioo (1/4 : ℝ) (1/3)) ∪
      bandSlice B.first (Ioo (2/3 : ℝ) (3/4)) ∪
      bandSlice B.second (Ioo (1/4 : ℝ) (1/3)) ∪
      bandSlice B.second (Ioo (2/3 : ℝ) (3/4)) := by
  ext x
  constructor
  · rintro ⟨hx, (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)⟩
    · rcases (first_mem_squareCollars_iff D B p).mp hx with h | h
      · exact Or.inl (Or.inl (Or.inl ⟨p, ⟨hp.1, h⟩, rfl⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨p, ⟨h, hp.2⟩, rfl⟩))
    · rcases (second_mem_squareCollars_iff D B p).mp hx with h | h
      · exact Or.inl (Or.inr ⟨p, ⟨hp.1, h⟩, rfl⟩)
      · exact Or.inr ⟨p, ⟨h, hp.2⟩, rfl⟩
  · rintro (((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩)
    · exact ⟨(first_mem_squareCollars_iff D B p).mpr (Or.inl hp.2),
        Or.inl ⟨p, ⟨hp.1, by linarith [hp.2]⟩, rfl⟩⟩
    · exact ⟨(first_mem_squareCollars_iff D B p).mpr (Or.inr hp.1),
        Or.inl ⟨p, ⟨by linarith [hp.1], hp.2⟩, rfl⟩⟩
    · exact ⟨(second_mem_squareCollars_iff D B p).mpr (Or.inl hp.2),
        Or.inr ⟨p, ⟨hp.1, by linarith [hp.2]⟩, rfl⟩⟩
    · exact ⟨(second_mem_squareCollars_iff D B p).mpr (Or.inr hp.1),
        Or.inr ⟨p, ⟨by linarith [hp.1], hp.2⟩, rfl⟩⟩

#print axioms squareCollars_middleBands_cover
#print axioms middleBands_relative_open
#print axioms squareCollars_middleBands_intersection
end CurveComplex.CapBandGeometry
