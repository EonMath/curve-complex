import RegionalWeightedMovieDefinitions

open CurveComplex Set Topology Schoenflies

/-- Filled widths between the guiding center and one literal rail in common coordinates. -/
def regionalHalfGuideSlab {S : Type} [TopologicalSpace S] (F : Set S)
    (E : C(Interval × Icc (-1 : ℝ) 1,↥F))
    (c : C(Interval,Interval × Icc (-1 : ℝ) 1)) : Set ↥F :=
  E '' {z | ∃ t : Interval, z.1 = (c t).1 ∧
    0 ≤ z.2.val ∧ z.2.val ≤ (c t).2.val}

/-- The explicit four vertices of the signed corner filling carrier. -/
def regionalHalfCornerHull (δ : ℝ) (entry : Plane) (ε : ℝ) : Set Plane :=
  convexHull ℝ ({0,Plane.mk (-δ) 0,entry,Plane.mk (entry 0-ε) (entry 1)} : Set Plane)

/-- A narrow negative half of the actual old strip on its padded prefix. -/
def regionalHalfOldNegativeBand {S : Type} [TopologicalSpace S] (F : Set S)
    (E : C(Interval × Icc (-1 : ℝ) 1,↥F))
    (clock : Interval ≃ₜ Interval) (cut : Interval) (width : ℝ) : Set ↥F :=
  E '' {z | z.1 ∈ clock '' Icc (0 : Interval) cut ∧
    -width ≤ z.2.val ∧ z.2.val ≤ 0}
