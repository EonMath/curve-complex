import CurveComplexGenusTwo.Cover.HemisphereDisk

namespace AlternatingSphereCover

abbrev StandardDisk := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
abbrev FourDisks := (Bool × StandardDisk) ⊕ (Bool × StandardDisk)

noncomputable def diskToNorth (x : Bool × StandardDisk) : NorthPiece :=
  let p := northHemisphereDiskHomeomorph.symm
    (coordinateDiskClosedBallHomeomorph.symm x.2)
  ⟨(p.val, x.1), p.property⟩

noncomputable def diskToSouth (x : Bool × StandardDisk) : SouthPiece :=
  let p := southHemisphereDiskHomeomorph.symm
    (coordinateDiskClosedBallHomeomorph.symm x.2)
  ⟨(p.val, x.1), p.property⟩

theorem diskToNorth_continuous : Continuous diskToNorth := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_subtype_val.comp
      (northHemisphereDiskHomeomorph.symm.continuous.comp
        (coordinateDiskClosedBallHomeomorph.symm.continuous.comp continuous_snd))
  · exact continuous_fst

theorem diskToSouth_continuous : Continuous diskToSouth := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_subtype_val.comp
      (southHemisphereDiskHomeomorph.symm.continuous.comp
        (coordinateDiskClosedBallHomeomorph.symm.continuous.comp continuous_snd))
  · exact continuous_fst

noncomputable def diskToPiece : FourDisks → HemispherePieces :=
  Sum.elim (fun x => Sum.inl (diskToNorth x))
    (fun x => Sum.inr (diskToSouth x))

theorem diskToPiece_continuous : Continuous diskToPiece := by
  apply continuous_sumElim.mpr
  exact ⟨continuous_inl.comp diskToNorth_continuous,
    continuous_inr.comp diskToSouth_continuous⟩

noncomputable def pieceToDisk : HemispherePieces → FourDisks :=
  Sum.elim
    (fun x => Sum.inl (x.val.2,
      coordinateDiskClosedBallHomeomorph
        (northHemisphereDiskHomeomorph ⟨x.val.1, x.property⟩)))
    (fun x => Sum.inr (x.val.2,
      coordinateDiskClosedBallHomeomorph
        (southHemisphereDiskHomeomorph ⟨x.val.1, x.property⟩)))

theorem pieceToDisk_diskToPiece (x : FourDisks) :
    pieceToDisk (diskToPiece x) = x := by
  cases x with
  | inl x =>
    rcases x with ⟨s, v⟩
    simp [pieceToDisk, diskToPiece, diskToNorth]
  | inr x =>
    rcases x with ⟨s, v⟩
    simp [pieceToDisk, diskToPiece, diskToSouth]

theorem diskToPiece_pieceToDisk (x : HemispherePieces) :
    diskToPiece (pieceToDisk x) = x := by
  cases x with
  | inl x =>
    rcases x with ⟨⟨p, s⟩, hp⟩
    simp [pieceToDisk, diskToPiece, diskToNorth]
  | inr x =>
    rcases x with ⟨⟨p, s⟩, hp⟩
    simp [pieceToDisk, diskToPiece, diskToSouth]

noncomputable def fourDisksEquivPieces : FourDisks ≃ HemispherePieces where
  toFun := diskToPiece
  invFun := pieceToDisk
  left_inv := pieceToDisk_diskToPiece
  right_inv := diskToPiece_pieceToDisk

noncomputable def fourDisksHomeomorphPieces : FourDisks ≃ₜ HemispherePieces :=
  (show Continuous (fourDisksEquivPieces : FourDisks → HemispherePieces) from
    diskToPiece_continuous).homeoOfEquivCompactToT2

def fourDiskSetoid : Setoid FourDisks where
  r x y := pieceSetoid (diskToPiece x) (diskToPiece y)
  iseqv := by
    have he : Equivalence (pieceSetoid.r) := pieceSetoid.iseqv
    constructor
    · intro x
      exact he.refl _
    · intro x y h
      exact he.symm h
    · intro x y z hxy hyz
      exact he.trans hxy hyz

/-- The actual surface as an attaching quotient of four standard closed
Euclidean 2-disks. -/
noncomputable def fourDiskQuotientHomeomorphTotal :
    Quotient fourDiskSetoid ≃ₜ Total :=
  (Homeomorph.Quotient.congr fourDisksHomeomorphPieces (by
    intro x y
    change pieceSetoid (diskToPiece x) (diskToPiece y) ↔
      pieceSetoid (diskToPiece x) (diskToPiece y)
    rfl)).trans piecesQuotientHomeomorphTotal

theorem fourDiskQuotient_north (sheet : Bool) (v : StandardDisk) :
    fourDiskQuotientHomeomorphTotal
      (Quotient.mk fourDiskSetoid (Sum.inl (sheet, v))) =
      northDiskFace sheet v := rfl

theorem fourDiskQuotient_south (sheet : Bool) (v : StandardDisk) :
    fourDiskQuotientHomeomorphTotal
      (Quotient.mk fourDiskSetoid (Sum.inr (sheet, v))) =
      southDiskFace sheet v := rfl

noncomputable def diskBoundaryPoint (p : Sphere) (_hp : height p = 0) :
    StandardDisk := coordinateDiskClosedBallHomeomorph (diskProjection p)

theorem northDiskFace_boundary (p : Sphere) (hp : height p = 0) (sheet : Bool) :
    northDiskFace sheet (diskBoundaryPoint p hp) =
      northCharacteristic (northBoundary p hp sheet) := by
  have h : northHemisphereDiskHomeomorph
      ⟨p, by simp [hp]⟩ = diskProjection p := rfl
  unfold northDiskFace diskBoundaryPoint northFace northBoundary
  rw [← h]
  simp

theorem southDiskFace_boundary (p : Sphere) (hp : height p = 0) (sheet : Bool) :
    southDiskFace sheet (diskBoundaryPoint p hp) =
      southCharacteristic (southBoundary p hp sheet) := by
  have h : southHemisphereDiskHomeomorph
      ⟨p, by simp [hp]⟩ = diskProjection p := rfl
  unfold southDiskFace diskBoundaryPoint southFace southBoundary
  rw [← h]
  simp

theorem fourDisk_sector_attachment {i : Fin 6} {p : Sphere}
    (h : arcSector i p) (s t : Bool) :
    (Quotient.mk fourDiskSetoid
      (Sum.inl (s, diskBoundaryPoint p h.1)) : Quotient fourDiskSetoid) =
      Quotient.mk fourDiskSetoid
        (Sum.inr (t, diskBoundaryPoint p h.1)) ↔
      t = if i.val % 2 = 0 then !s else s := by
  rw [← fourDiskQuotientHomeomorphTotal.injective.eq_iff,
    fourDiskQuotient_north, fourDiskQuotient_south,
    northDiskFace_boundary, southDiskFace_boundary]
  exact sector_attachment h s t

end AlternatingSphereCover
