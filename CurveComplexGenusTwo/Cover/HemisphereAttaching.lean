import CurveComplexGenusTwo.Cover.EquatorGluing
import Mathlib.Topology.Homeomorph.Quotient

namespace AlternatingSphereCover

/-- Two copies of each closed hemisphere, before attaching the banks. -/
abbrev NorthPiece := {p : Sphere × Bool // 0 ≤ height p.1}
abbrev SouthPiece := {p : Sphere × Bool // height p.1 ≤ 0}
abbrev HemispherePieces := NorthPiece ⊕ SouthPiece

def pieceToRaw : HemispherePieces → Raw := Sum.elim
  (fun x => ⟨(x.val.1, true, x.val.2), x.property⟩)
  (fun x => ⟨(x.val.1, false, x.val.2), x.property⟩)

theorem pieceToRaw_continuous : Continuous pieceToRaw := by
  apply continuous_sumElim.mpr
  constructor
  · apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · exact continuous_const.prodMk (continuous_snd.comp continuous_subtype_val)
  · apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · exact continuous_const.prodMk (continuous_snd.comp continuous_subtype_val)

def rawToPiece (x : Raw) : HemispherePieces :=
  if h : x.val.2.1 then
    Sum.inl ⟨(x.val.1, x.val.2.2), by simpa [h] using x.property⟩
  else
    Sum.inr ⟨(x.val.1, x.val.2.2), by simpa [h] using x.property⟩

theorem pieceToRaw_rawToPiece (x : Raw) : pieceToRaw (rawToPiece x) = x := by
  rcases x with ⟨⟨p, b, s⟩, hp⟩
  cases b <;> rfl

theorem rawToPiece_pieceToRaw (x : HemispherePieces) :
    rawToPiece (pieceToRaw x) = x := by
  cases x with
  | inl x => simp [rawToPiece, pieceToRaw]
  | inr x => simp [rawToPiece, pieceToRaw]

private instance : CompactSpace NorthPiece := by
  have hc : IsClosed {p : Sphere × Bool | 0 ≤ height p.1} :=
    isClosed_le continuous_const (height_continuous.comp continuous_fst)
  exact isCompact_iff_compactSpace.mp hc.isCompact

private instance : CompactSpace SouthPiece := by
  have hc : IsClosed {p : Sphere × Bool | height p.1 ≤ 0} :=
    isClosed_le (height_continuous.comp continuous_fst) continuous_const
  exact isCompact_iff_compactSpace.mp hc.isCompact

def piecesEquivRaw : HemispherePieces ≃ Raw where
  toFun := pieceToRaw
  invFun := rawToPiece
  left_inv := rawToPiece_pieceToRaw
  right_inv := pieceToRaw_rawToPiece

noncomputable def piecesHomeomorphRaw : HemispherePieces ≃ₜ Raw :=
  (show Continuous (piecesEquivRaw : HemispherePieces → Raw) from
    pieceToRaw_continuous).homeoOfEquivCompactToT2

/-- The actual bank identification, expressed on the disjoint union of
the northern and southern two-sheet hemispheres. -/
def pieceSetoid : Setoid HemispherePieces where
  r x y := Rel (pieceToRaw x) (pieceToRaw y)
  iseqv := by
    have he : Equivalence Rel := setoid.iseqv
    constructor
    · intro x
      exact he.refl _
    · intro x y h
      exact he.symm h
    · intro x y z hxy hyz
      exact he.trans hxy hyz

/-- An actual attaching-space presentation of `Total`. -/
noncomputable def piecesQuotientHomeomorphTotal :
    Quotient pieceSetoid ≃ₜ Total :=
  Homeomorph.Quotient.congr piecesHomeomorphRaw (by
    intro x y
    change Rel (pieceToRaw x) (pieceToRaw y) ↔
      Rel (pieceToRaw x) (pieceToRaw y)
    rfl)

/-- Characteristic maps of the two pairs of closed hemisphere faces. -/
def northCharacteristic (x : NorthPiece) : Total :=
  Quotient.mk setoid (pieceToRaw (Sum.inl x))

def southCharacteristic (x : SouthPiece) : Total :=
  Quotient.mk setoid (pieceToRaw (Sum.inr x))

theorem northCharacteristic_continuous : Continuous northCharacteristic := by
  exact continuous_quotient_mk'.comp
    (pieceToRaw_continuous.comp continuous_inl)

theorem southCharacteristic_continuous : Continuous southCharacteristic := by
  exact continuous_quotient_mk'.comp
    (pieceToRaw_continuous.comp continuous_inr)

theorem projection_northCharacteristic (x : NorthPiece) :
    projection (northCharacteristic x) = x.val.1 := rfl

theorem projection_southCharacteristic (x : SouthPiece) :
    projection (southCharacteristic x) = x.val.1 := rfl

theorem north_south_intersection {x : NorthPiece} {y : SouthPiece}
    (h : northCharacteristic x = southCharacteristic y) :
    x.val.1 = y.val.1 ∧ height x.val.1 = 0 := by
  have hp := congrArg projection h
  have hbase : x.val.1 = y.val.1 := by
    simpa only [projection_northCharacteristic, projection_southCharacteristic] using hp
  refine ⟨hbase, ?_⟩
  have hy : height x.val.1 ≤ 0 := hbase ▸ y.property
  exact le_antisymm hy x.property

abbrev NorthHemisphere := {p : Sphere // 0 ≤ height p}
abbrev SouthHemisphere := {p : Sphere // height p ≤ 0}

/-- Four face maps, indexed by hemisphere and sheet. -/
def northFace (sheet : Bool) (p : NorthHemisphere) : Total :=
  northCharacteristic ⟨(p.val, sheet), p.property⟩

def southFace (sheet : Bool) (p : SouthHemisphere) : Total :=
  southCharacteristic ⟨(p.val, sheet), p.property⟩

theorem northFace_continuous (sheet : Bool) : Continuous (northFace sheet) := by
  apply northCharacteristic_continuous.comp
  apply Continuous.subtype_mk
  exact continuous_subtype_val.prodMk continuous_const

theorem southFace_continuous (sheet : Bool) : Continuous (southFace sheet) := by
  apply southCharacteristic_continuous.comp
  apply Continuous.subtype_mk
  exact continuous_subtype_val.prodMk continuous_const

theorem projection_northFace (sheet : Bool) (p : NorthHemisphere) :
    projection (northFace sheet p) = p.val := rfl

theorem projection_southFace (sheet : Bool) (p : SouthHemisphere) :
    projection (southFace sheet p) = p.val := rfl

theorem northFace_injective (sheet : Bool) : Function.Injective (northFace sheet) := by
  intro p q h
  apply Subtype.ext
  have hp := congrArg projection h
  simpa only [projection_northFace] using hp

theorem southFace_injective (sheet : Bool) : Function.Injective (southFace sheet) := by
  intro p q h
  apply Subtype.ext
  have hp := congrArg projection h
  simpa only [projection_southFace] using hp

def northBoundary (p : Sphere) (hp : height p = 0) (sheet : Bool) : NorthPiece :=
  ⟨(p, sheet), by simp [hp]⟩

def southBoundary (p : Sphere) (hp : height p = 0) (sheet : Bool) : SouthPiece :=
  ⟨(p, sheet), by simp [hp]⟩

theorem boundary_attach (p : Sphere) (hp : height p = 0) (s t : Bool) :
    northCharacteristic (northBoundary p hp s) =
      southCharacteristic (southBoundary p hp t) ↔
      branch p ∨ t = s ^^ decide (0 < seamPolynomial p) := by
  change (Quotient.mk setoid (equatorRaw p hp true s) : Total) =
    Quotient.mk setoid (equatorRaw p hp false t) ↔ _
  exact equator_glue p hp s t

theorem north_interior_injective {x y : NorthPiece}
    (hx : 0 < height x.val.1)
    (hxy : northCharacteristic x = northCharacteristic y) : x = y := by
  have hr : Rel (pieceToRaw (Sum.inl x)) (pieceToRaw (Sum.inl y)) := by
    change (Quotient.mk setoid (pieceToRaw (Sum.inl x)) : Total) =
      Quotient.mk setoid (pieceToRaw (Sum.inl y)) at hxy
    rw [Quotient.eq] at hxy
    exact hxy
  have hbase : x.val.1 = y.val.1 := hr.1
  have hnbranch : ¬ branch x.val.1 := by
    intro hb
    exact (ne_of_gt hx) hb.1
  have hs : x.val.2 = y.val.2 := by
    rcases hr.2 with hb | hl
    · exact False.elim (hnbranch hb)
    · by_cases h : 0 < seamPolynomial y.val.1
      · simpa [pieceToRaw, label, hbase, h] using hl
      · simpa [pieceToRaw, label, hbase, h] using hl
  apply Subtype.ext
  exact Prod.ext hbase hs

theorem south_interior_injective {x y : SouthPiece}
    (hx : height x.val.1 < 0)
    (hxy : southCharacteristic x = southCharacteristic y) : x = y := by
  have hr : Rel (pieceToRaw (Sum.inr x)) (pieceToRaw (Sum.inr y)) := by
    change (Quotient.mk setoid (pieceToRaw (Sum.inr x)) : Total) =
      Quotient.mk setoid (pieceToRaw (Sum.inr y)) at hxy
    rw [Quotient.eq] at hxy
    exact hxy
  have hbase : x.val.1 = y.val.1 := hr.1
  have hnbranch : ¬ branch x.val.1 := by
    intro hb
    exact (ne_of_lt hx) hb.1
  have hs : x.val.2 = y.val.2 := by
    rcases hr.2 with hb | hl
    · exact False.elim (hnbranch hb)
    · simpa [pieceToRaw, label] using hl
  apply Subtype.ext
  exact Prod.ext hbase hs

end AlternatingSphereCover
