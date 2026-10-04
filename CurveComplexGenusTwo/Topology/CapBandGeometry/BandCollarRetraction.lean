import CurveComplexGenusTwo.Topology.CapBandGeometry.BandCoverComponents

open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

/-- Finite closed-set pasting, used for the literal square/band attachments. -/
noncomputable def finiteClosedCoverMap
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (C : ι → Set X) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ⋃ i, C i = Set.univ) (φ : ∀ i, C(C i, Y))
    (hagree : ∀ i j x (hi : x ∈ C i) (hj : x ∈ C j), φ i ⟨x, hi⟩ = φ j ⟨x, hj⟩) :
    C(X, Y) := by
  let f := Set.liftCover C (fun i => φ i) hagree hcover
  refine ⟨f, (locallyFinite_of_finite C).continuous hcover hclosed ?_⟩
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (C i).domRestrict f = φ i := by
    funext x
    exact Set.liftCover_coe (S := C) (f := fun i => φ i) (hf := hagree) (hS := hcover) x
  rw [heq]
  exact (φ i).continuous

@[simp] theorem finiteClosedCoverMap_apply
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (C : ι → Set X) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ⋃ i, C i = Set.univ) (φ : ∀ i, C(C i, Y))
    (hagree : ∀ i j x (hi : x ∈ C i) (hj : x ∈ C j), φ i ⟨x, hi⟩ = φ j ⟨x, hj⟩)
    (i : ι) (x : C i) : finiteClosedCoverMap C hclosed hcover φ hagree x = φ i x :=
  Set.liftCover_coe (S := C) (f := fun i => φ i) (hf := hagree) (hS := hcover) x

/-- A continuous longitudinal collapse, keeping both attachment ends fixed. -/
noncomputable def longitudinalCollapse (s t : I) : I :=
  ⟨(1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) *
      (projIcc 0 1 zero_le_one (3 * (t : ℝ) - 1) : ℝ), by
    have hc := (projIcc 0 1 zero_le_one (3 * (t : ℝ) - 1)).property
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) t.property.1)
        (mul_nonneg s.property.1 hc.1)
    · nlinarith [s.property.1, s.property.2, t.property.1, t.property.2,
        hc.1, hc.2, mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr t.property.2),
        mul_nonneg s.property.1 (sub_nonneg.mpr hc.2)]⟩

@[fun_prop] theorem longitudinalCollapse_continuous :
    Continuous (fun p : I × I => longitudinalCollapse p.1 p.2) := by
  unfold longitudinalCollapse
  fun_prop

@[simp] theorem longitudinalCollapse_zero_time (t : I) : longitudinalCollapse 0 t = t := by
  apply Subtype.ext
  simp [longitudinalCollapse]

@[simp] theorem longitudinalCollapse_zero_end (s : I) : longitudinalCollapse s 0 = 0 := by
  apply Subtype.ext
  simp [longitudinalCollapse, projIcc_of_le_left]

@[simp] theorem longitudinalCollapse_one_end (s : I) : longitudinalCollapse s 1 = 1 := by
  apply Subtype.ext
  have hp : projIcc (0 : ℝ) 1 zero_le_one 2 = (1 : I) :=
    projIcc_of_right_le zero_le_one (by norm_num)
  simp [longitudinalCollapse]
  rw [show (3 : ℝ) - 1 = 2 by norm_num, hp]
  simp


theorem longitudinalCollapse_lower (s t : I) (ht : (t : ℝ) < 1/3) :
    (longitudinalCollapse s t : ℝ) = (1 - (s : ℝ)) * (t : ℝ) := by
  simp only [longitudinalCollapse]
  rw [projIcc_of_le_left zero_le_one (by linarith : 3 * (t : ℝ) - 1 ≤ 0)]
  simp

theorem longitudinalCollapse_upper (s t : I) (ht : 2/3 < (t : ℝ)) :
    (longitudinalCollapse s t : ℝ) = (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) := by
  simp only [longitudinalCollapse]
  rw [projIcc_of_right_le zero_le_one (by linarith : 1 ≤ 3 * (t : ℝ) - 1)]
  simp

theorem longitudinalCollapse_preserves_ends (s t : I)
    (ht : (t : ℝ) < 1/3 ∨ 2/3 < (t : ℝ)) :
    (longitudinalCollapse s t : ℝ) < 1/3 ∨ 2/3 < (longitudinalCollapse s t : ℝ) := by
  rcases ht with ht | ht
  · left
    rw [longitudinalCollapse_lower s t ht]
    have hst : 0 ≤ (s : ℝ) * (t : ℝ) := mul_nonneg s.property.1 t.property.1
    nlinarith
  · right
    rw [longitudinalCollapse_upper s t ht]
    have hst : 0 ≤ (s : ℝ) * (1 - (t : ℝ)) :=
      mul_nonneg s.property.1 (sub_nonneg.mpr t.property.2)
    nlinarith

theorem longitudinalCollapse_one_time (t : I)
    (ht : (t : ℝ) < 1/3 ∨ 2/3 < (t : ℝ)) :
    longitudinalCollapse 1 t = 0 ∨ longitudinalCollapse 1 t = 1 := by
  rcases ht with ht | ht
  · left
    apply Subtype.ext
    rw [longitudinalCollapse_lower 1 t ht]
    norm_num
  · right
    apply Subtype.ext
    rw [longitudinalCollapse_upper 1 t ht]
    norm_num

/-- The collapse on one supplied band, defined on its actual embedded image. -/
noncomputable def bandLongitudinalMap {S : Type*} [TopologicalSpace S]
    (F : I × BandWidth → S) (hF : IsEmbedding F) : C(I × Set.range F, S) := {
  toFun := fun p => F (longitudinalCollapse p.1 (hF.toHomeomorph.symm p.2).1,
    (hF.toHomeomorph.symm p.2).2)
  continuous_toFun := by
    apply hF.continuous.comp
    exact (longitudinalCollapse_continuous.comp
      (continuous_fst.prodMk ((continuous_fst.comp hF.toHomeomorph.symm.continuous).comp
        continuous_snd))).prodMk
      ((continuous_snd.comp hF.toHomeomorph.symm.continuous).comp continuous_snd) }

@[simp] theorem bandLongitudinalMap_apply {S : Type*} [TopologicalSpace S]
    (F : I × BandWidth → S) (hF : IsEmbedding F) (s : I) (p : I × BandWidth) :
    bandLongitudinalMap F hF (s, ⟨F p, Set.mem_range_self p⟩) =
      F (longitudinalCollapse s p.1, p.2) := by
  change F (longitudinalCollapse s (hF.toHomeomorph.symm (hF.toHomeomorph p)).1,
    (hF.toHomeomorph.symm (hF.toHomeomorph p)).2) = _
  rw [hF.toHomeomorph.symm_apply_apply]

#print axioms longitudinalCollapse_preserves_ends
#print axioms bandLongitudinalMap
end CurveComplex.CapBandGeometry

namespace CurveComplex.CapBandGeometry

/-- The longitudinal contraction agrees with the square map on every actual
attachment seam, not merely on the centerline. -/
theorem first_collapse_fixes_square {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (s : I) (p : I × BandWidth) (hp : B.first p ∈ Set.range D.square) :
    B.first (longitudinalCollapse s p.1, p.2) = B.first p := by
  rcases (first_mem_square_iff D B p).mp hp with h | h
  · rw [h, longitudinalCollapse_zero_end]
    exact congrArg B.first (Prod.ext h.symm rfl)
  · rw [h, longitudinalCollapse_one_end]
    exact congrArg B.first (Prod.ext h.symm rfl)

theorem second_collapse_fixes_square {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (s : I) (p : I × BandWidth) (hp : B.second p ∈ Set.range D.square) :
    B.second (longitudinalCollapse s p.1, p.2) = B.second p := by
  rcases (second_mem_square_iff D B p).mp hp with h | h
  · rw [h, longitudinalCollapse_zero_end]
    exact congrArg B.second (Prod.ext h.symm rfl)
  · rw [h, longitudinalCollapse_one_end]
    exact congrArg B.second (Prod.ext h.symm rfl)

/-- The actual three closed pieces used to paste the contraction. -/
def contractionPiece {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (i : Fin 3) : Set (I × bandUnion D B) :=
  {p | if i = 0 then (p.2 : S) ∈ Set.range D.square
      else if i = 1 then (p.2 : S) ∈ Set.range B.first
      else (p.2 : S) ∈ Set.range B.second}

theorem contractionPiece_closed {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (i : Fin 3) : IsClosed (contractionPiece D B i) := by
  fin_cases i
  · exact (isCompact_range D.square_embedded.continuous).isClosed.preimage
      (continuous_subtype_val.comp continuous_snd)
  · exact (isCompact_range B.first_embedded.continuous).isClosed.preimage
      (continuous_subtype_val.comp continuous_snd)
  · exact (isCompact_range B.second_embedded.continuous).isClosed.preimage
      (continuous_subtype_val.comp continuous_snd)

theorem contractionPiece_cover {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    (⋃ i : Fin 3, contractionPiece D B i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  rcases p.2.property with (hp | hp) | hp
  · exact Set.mem_iUnion.mpr ⟨0, hp⟩
  · exact Set.mem_iUnion.mpr ⟨1, hp⟩
  · exact Set.mem_iUnion.mpr ⟨2, hp⟩

noncomputable def contractionPieceMap {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (i : Fin 3) : C(contractionPiece D B i, S) := by
  by_cases h0 : i = 0
  · exact ⟨fun p => p.1.2.1, by fun_prop⟩
  · by_cases h1 : i = 1
    · let q : contractionPiece D B i → I × Set.range B.first :=
        fun p => (p.1.1, ⟨p.1.2.1, by simpa [contractionPiece, h0, h1] using p.2⟩)
      exact (bandLongitudinalMap B.first B.first_embedded).comp ⟨q, by fun_prop⟩
    · let q : contractionPiece D B i → I × Set.range B.second :=
        fun p => (p.1.1, ⟨p.1.2.1, by simpa [contractionPiece, h0, h1] using p.2⟩)
      exact (bandLongitudinalMap B.second B.second_embedded).comp ⟨q, by fun_prop⟩

@[simp] theorem contractionPieceMap_zero {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (p : contractionPiece D B 0) : contractionPieceMap D B 0 p = p.1.2.1 := by
  simp [contractionPieceMap]

@[simp] theorem contractionPieceMap_one {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (p : contractionPiece D B 1) : contractionPieceMap D B 1 p =
      bandLongitudinalMap B.first B.first_embedded
        (p.1.1, ⟨p.1.2.1, by simpa [contractionPiece] using p.2⟩) := by
  simp [contractionPieceMap]

@[simp] theorem contractionPieceMap_two {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (p : contractionPiece D B 2) : contractionPieceMap D B 2 p =
      bandLongitudinalMap B.second B.second_embedded
        (p.1.1, ⟨p.1.2.1, by simpa [contractionPiece] using p.2⟩) := by
  simp [contractionPieceMap]

theorem contractionPieceMap_agree {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (i j : Fin 3) (x : I × bandUnion D B)
    (hi : x ∈ contractionPiece D B i) (hj : x ∈ contractionPiece D B j) :
    contractionPieceMap D B i ⟨x, hi⟩ = contractionPieceMap D B j ⟨x, hj⟩ := by
  have h01 (h0 : x ∈ contractionPiece D B 0) (h1 : x ∈ contractionPiece D B 1) :
      contractionPieceMap D B 0 ⟨x, h0⟩ = contractionPieceMap D B 1 ⟨x, h1⟩ := by
    simp only [contractionPieceMap_zero, contractionPieceMap_one]
    obtain ⟨p, hp⟩ := h1
    have hxp : (x.2 : S) = B.first p := hp.symm
    have hsq : B.first p ∈ Set.range D.square := hxp ▸ h0
    simp only [hxp]
    rw [bandLongitudinalMap_apply]
    exact (first_collapse_fixes_square D B x.1 p hsq).symm
  have h02 (h0 : x ∈ contractionPiece D B 0) (h2 : x ∈ contractionPiece D B 2) :
      contractionPieceMap D B 0 ⟨x, h0⟩ = contractionPieceMap D B 2 ⟨x, h2⟩ := by
    simp only [contractionPieceMap_zero, contractionPieceMap_two]
    obtain ⟨p, hp⟩ := h2
    have hxp : (x.2 : S) = B.second p := hp.symm
    have hsq : B.second p ∈ Set.range D.square := hxp ▸ h0
    simp only [hxp]
    rw [bandLongitudinalMap_apply]
    exact (second_collapse_fixes_square D B x.1 p hsq).symm
  have h12 (h1 : x ∈ contractionPiece D B 1) (h2 : x ∈ contractionPiece D B 2) : False :=
    Set.disjoint_left.mp B.bands_disjoint h1 h2
  fin_cases i <;> fin_cases j
  · rfl
  · exact h01 hi hj
  · exact h02 hi hj
  · exact (h01 hj hi).symm
  · rfl
  · exact (h12 hi hj).elim
  · exact (h02 hj hi).symm
  · exact (h12 hj hi).elim
  · rfl

noncomputable def bandUnionLongitudinalMap {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    C(I × bandUnion D B, S) :=
  finiteClosedCoverMap (contractionPiece D B) (contractionPiece_closed D B)
    (contractionPiece_cover D B) (contractionPieceMap D B) (contractionPieceMap_agree D B)

end CurveComplex.CapBandGeometry

namespace CurveComplex.CapBandGeometry

@[simp] theorem bandUnionLongitudinalMap_on_square {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (s : I) (x : bandUnion D B) (hx : (x : S) ∈ Set.range D.square) :
    bandUnionLongitudinalMap D B (s, x) = (x : S) := by
  exact (finiteClosedCoverMap_apply _ _ _ _ _ 0 ⟨(s, x), hx⟩).trans
    (contractionPieceMap_zero D B _)

@[simp] theorem bandUnionLongitudinalMap_on_first {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (s : I) (p : I × BandWidth) :
    bandUnionLongitudinalMap D B
      (s, ⟨B.first p, Or.inl (Or.inr (Set.mem_range_self p))⟩) =
      B.first (longitudinalCollapse s p.1, p.2) := by
  have hh := finiteClosedCoverMap_apply (contractionPiece D B) (contractionPiece_closed D B)
    (contractionPiece_cover D B) (contractionPieceMap D B) (contractionPieceMap_agree D B)
    1 ⟨(s, ⟨B.first p, Or.inl (Or.inr (Set.mem_range_self p))⟩), Set.mem_range_self p⟩
  exact hh.trans ((contractionPieceMap_one D B _).trans
    (bandLongitudinalMap_apply B.first B.first_embedded s p))

@[simp] theorem bandUnionLongitudinalMap_on_second {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (s : I) (p : I × BandWidth) :
    bandUnionLongitudinalMap D B
      (s, ⟨B.second p, Or.inr (Set.mem_range_self p)⟩) =
      B.second (longitudinalCollapse s p.1, p.2) := by
  have hh := finiteClosedCoverMap_apply (contractionPiece D B) (contractionPiece_closed D B)
    (contractionPiece_cover D B) (contractionPieceMap D B) (contractionPieceMap_agree D B)
    2 ⟨(s, ⟨B.second p, Or.inr (Set.mem_range_self p)⟩), Set.mem_range_self p⟩
  exact hh.trans ((contractionPieceMap_two D B _).trans
    (bandLongitudinalMap_apply B.second B.second_embedded s p))

theorem square_subset_squareCollars {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    Set.range D.square ⊆ squareCollars D B := by
  intro x hx
  refine ⟨Or.inl (Or.inl hx), ?_⟩
  rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
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

/-- The pasted contraction preserves the literal square-with-end-collars set. -/
theorem bandUnionLongitudinalMap_preserves_squareCollars
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (s : I) (x : bandUnion D B) (hx : (x : S) ∈ squareCollars D B) :
    bandUnionLongitudinalMap D B (s, x) ∈ squareCollars D B := by
  rcases x with ⟨x, (hxD | ⟨p, rfl⟩) | ⟨p, rfl⟩⟩
  · rw [bandUnionLongitudinalMap_on_square D B s _ hxD]
    exact hx
  · rw [bandUnionLongitudinalMap_on_first]
    apply (first_mem_squareCollars_iff D B _).mpr
    exact longitudinalCollapse_preserves_ends s p.1 ((first_mem_squareCollars_iff D B p).mp hx)
  · rw [bandUnionLongitudinalMap_on_second]
    apply (second_mem_squareCollars_iff D B _).mpr
    exact longitudinalCollapse_preserves_ends s p.1 ((second_mem_squareCollars_iff D B p).mp hx)

/-- At time one, every end-collar point is on an actual attachment port of the square. -/
theorem bandUnionLongitudinalMap_squareCollars_one
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (x : bandUnion D B) (hx : (x : S) ∈ squareCollars D B) :
    bandUnionLongitudinalMap D B (1, x) ∈ Set.range D.square := by
  rcases x with ⟨x, (hxD | ⟨p, rfl⟩) | ⟨p, rfl⟩⟩
  · rw [bandUnionLongitudinalMap_on_square D B 1 _ hxD]
    exact hxD
  · rw [bandUnionLongitudinalMap_on_first]
    exact (first_mem_square_iff D B _).mpr
      (longitudinalCollapse_one_time p.1 ((first_mem_squareCollars_iff D B p).mp hx))
  · rw [bandUnionLongitudinalMap_on_second]
    exact (second_mem_square_iff D B _).mpr
      (longitudinalCollapse_one_time p.1 ((second_mem_squareCollars_iff D B p).mp hx))

#print axioms bandUnionLongitudinalMap
#print axioms bandUnionLongitudinalMap_preserves_squareCollars
#print axioms bandUnionLongitudinalMap_squareCollars_one
end CurveComplex.CapBandGeometry

namespace CurveComplex.CapBandGeometry

@[simp] theorem bandUnionLongitudinalMap_zero {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    (x : bandUnion D B) : bandUnionLongitudinalMap D B (0, x) = (x : S) := by
  rcases x with ⟨x, (hxD | ⟨p, rfl⟩) | ⟨p, rfl⟩⟩
  · exact bandUnionLongitudinalMap_on_square D B 0 _ hxD
  · rw [bandUnionLongitudinalMap_on_first, longitudinalCollapse_zero_time]
  · rw [bandUnionLongitudinalMap_on_second, longitudinalCollapse_zero_time]

/-- The literal square-with-four-end-collars retracts through a homotopy
onto the image of the same supplied square. -/
noncomputable def squareCollarsSquareHomotopyEquiv
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    ContinuousMap.HomotopyEquiv (squareCollars D B) (Set.range D.square) := by
  let incN : C(squareCollars D B, bandUnion D B) :=
    ⟨fun x => ⟨x.1, x.2.1⟩, by fun_prop⟩
  let r : C(squareCollars D B, Set.range D.square) := {
    toFun := fun x => ⟨bandUnionLongitudinalMap D B (1, incN x),
      bandUnionLongitudinalMap_squareCollars_one D B (incN x) x.2⟩
    continuous_toFun := by fun_prop }
  let inc : C(Set.range D.square, squareCollars D B) :=
    ⟨fun x => ⟨x.1, square_subset_squareCollars D B x.2⟩, by fun_prop⟩
  have hhom : (ContinuousMap.id (squareCollars D B)).Homotopic (inc.comp r) := by
    refine ⟨{
      toFun := fun p => ⟨bandUnionLongitudinalMap D B (p.1, incN p.2),
        bandUnionLongitudinalMap_preserves_squareCollars D B p.1 (incN p.2) p.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      apply Subtype.ext
      exact bandUnionLongitudinalMap_zero D B (incN x)
    · intro x
      rfl
  have hright : r.comp inc = ContinuousMap.id (Set.range D.square) := by
    ext x
    exact bandUnionLongitudinalMap_on_square D B 1 _ x.2
  exact ⟨r, inc, hhom.symm, hright ▸ ContinuousMap.Homotopic.refl _⟩

/-- The square-and-four-collars member of the literal homology cover is
contractible, derived from the actual maps and seam identities. -/
theorem squareCollars_contractible
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    ContractibleSpace (squareCollars D B) := by
  letI : ContractibleSpace (Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius) :=
    Metric.contractibleSpace_closedBall D.radius_pos.le
  letI : ContractibleSpace (Set.range D.square) := D.square_embedded.toHomeomorph.symm.contractibleSpace
  exact (squareCollarsSquareHomotopyEquiv D B).contractibleSpace

#print axioms squareCollarsSquareHomotopyEquiv
#print axioms squareCollars_contractible
end CurveComplex.CapBandGeometry
